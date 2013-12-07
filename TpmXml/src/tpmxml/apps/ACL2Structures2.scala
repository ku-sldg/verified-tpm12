package tpmxml.apps

import tpmxml.data._
import tpmxml.util.CaseConverter._

/**
 * Creates an ACL2 file (*.lisp) that contains all the structures from the TPM XML file.
 *
 *  The structures are broken down into four kinds:
 *
 *  (1) records -- those with fields
 *  (2) enums -- those with values
 *  (3) flags -- those with bit values
 *  (4) redefs -- those with neither fields nor values
 *
 *  In ACL2, these structures take the following form:
 *
 * ;; Record
 * (cutil::defaggregate name
 *   ((fieldname1 fieldtype1-p)
 *    (fieldname2 fieldtype2-p)))
 *
 * ;; Enum
 * (cutil::defenum name-p
 *   (:valuename1
 *    :valuename2))
 *
 * ;; Flag
 * (cutil::defaggregate name
 *   ((bitvalue1 booleanp)
 *    (bitvalue2 booleanp)))
 *
 * ;; Redef
 * (defn name-p (x)
 *   (redefname-p x))
 */
object ACL2Structures2 {

    // ==========================================================
    // Input Files
    // ==========================================================

    val TPMStructuresXMLFile = "resources/tpm-structures-2.xml"
    val PrimitiveTypesACL2File = "resources/primitive-types.lisp"

    // ==========================================================
    // Output Files
    // ==========================================================

    val TCGStructuresACL2File = "resources/tcg-structures-2.lisp"

    // ==========================================================
    // Main method
    // ==========================================================    

    def main(args: Array[String]) {

        val FixedByteArray = """BYTE\[(\d+)\]""".r
        val commentBar = "; ==============================================================="

        val pcrAndDigestLists = "\n(cutil::deflist tpm-pcrvalue-list-p (x)\n" +
        		"  (tpm-pcrvalue-p x)\n" +
        		"  :elementp-of-nil nil\n" +
        		"  :true-listp t)\n\n" +
        		"(cutil::deflist tpm-digest-list-p (x)\n" +
        		"  (tpm-digest-p x)\n" +
        		"  :elementp-of-nil nil\n" +
        		"  :true-listp t)\n"
            
        def header(s: String) = "\n" + commentBar + "\n; " + s + "\n" + commentBar + "\n\n"

        def acl2Predicate(tcgType: String): String = {
            tcgType match {
                case "BOOL" => "booleanp"
                case FixedByteArray(n) => n.toString + "-byte-list-p"
                case "BYTE[]" | "BYTE*" => "byte-list-p"
                case "TPM_PCRVALUE[]" => "tpm-pcrvalue-list-p"
                case "TPM_DIGEST[]" => "tpm-digest-list-p"
                case x => snakeToDash(x) + "-p"
            }
        }

        def getAcl2Redef(s: TpmStructure): String = {
            "(defn " + snakeToDash(s.name) + "-p (x)\n  (" + acl2Predicate(s.typedef) + " x))\n"
        }

        def acl2Symbol(s: String): String = s.toLowerCase match {
            case "reserved" | "unused" | "open" => ";; " + s
            case "xx" => "#| " + s + " |#"
            case _ => ":" + snakeToDash(s)         
        }
        
        def getAcl2Enum(s: TpmStructure): String = {
            val strs: List[String] = s.values.map(v => acl2Symbol(v.name))
            val str = strs.mkString("  (", "\n   ", "))\n")
            "(cutil::defenum " + snakeToDash(s.name) + "-p\n" + str
        }

        def getAcl2Flag(s: TpmStructure): String = {
            val strs: List[String] = s.values.map(v => snakeToDash(v.name) + " booleanp")
            val str = strs.mkString("  ((", ")\n   (", ")))\n")
            "(cutil::defaggregate " + snakeToDash(s.name) + "\n" + str
        }

        def getAcl2Record(s: TpmStructure): String = {
            val strs: List[String] = s.fields.map(f => camelToDash(f.name) + " " + acl2Predicate(f.typeName))
            val str = strs.mkString("  ((", ")\n   (", ")))\n")
            "(cutil::defaggregate " + snakeToDash(s.name) + "\n" + str
        }

        val tpmStructuresXml = xml.XML.loadFile(TPMStructuresXMLFile)
        val structures: List[TpmStructure] = (tpmStructuresXml \ "structure").map(TpmStructure.fromXML(_)).toList

        val (recordStructures, nonRecordStructures) = structures.partition(s => s.fields.nonEmpty)
        val (redefStructures, enumAndFlagStructures) = nonRecordStructures.partition(s => s.values.isEmpty)
        val (flagStructures, enumStructures) = enumAndFlagStructures.partition(s => s.valuesKind == "bit")

        val acl2Records = recordStructures.map(s => getAcl2Record(s)).mkString("\n")
        val acl2Enums = enumStructures.map(s => getAcl2Enum(s)).mkString("\n")
        val acl2Flags = flagStructures.map(s => getAcl2Flag(s)).mkString("\n")
        val acl2Redefs = redefStructures.map(s => getAcl2Redef(s)).mkString("\n")

        val primitiveTypesFile = scala.io.Source.fromFile(PrimitiveTypesACL2File)
        val primitiveTypesString = primitiveTypesFile.mkString
        primitiveTypesFile.close()

        val fileContents = primitiveTypesString + pcrAndDigestLists +
            header("Wrappers") + acl2Redefs +
            header("Flags") + acl2Flags +
            header("Enumerations") + acl2Enums +
            header("Records") + acl2Records

        val out = new java.io.FileWriter(TCGStructuresACL2File)
        out.write(fileContents)
        out.close
    }
}
