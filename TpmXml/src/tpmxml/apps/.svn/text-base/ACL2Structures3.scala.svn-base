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
object ACL2Structures3 {

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
            
        val descMax = 100
            
        def header(s: String) = "\n" + commentBar + "\n; " + s + "\n" + commentBar + "\n\n"
        
        def spaces(s: String, to: Int): String = " " * (to - s.length())

        val pcrAndDigestLists = header("TPM_PCRVALUE[] and TPM_DIGEST[]") +
            "(cutil::deflist tpm-pcrvalue-list-p (x)\n" +
            "  (tpm-pcrvalue-p x)\n" +
            "  :elementp-of-nil nil\n" +
            "  :true-listp t)\n\n" +
            "(cutil::deflist tpm-digest-list-p (x)\n" +
            "  (tpm-digest-p x)\n" +
            "  :elementp-of-nil nil\n" +
            "  :true-listp t)\n"

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

        def descAbbrev(desc: String): String =
            if (desc.length > descMax) {
                desc.trim.take(descMax) + " ..."
            } else {
                desc.trim
            }

        def acl2Symbol(s: String): String = s.toLowerCase match {
            case "reserved" | "unused" | "open" | "xx" => ";; " + s
            case _ => ":" + snakeToDash(s)
        }
        
        def intro(s: TpmStructure) = ";; " + s.section + " " + s.name +
        		{ if (s.description != "") "\n;; " + descAbbrev(s.description) } + "\n"

        def fieldToDash(s: String) = if (s.contains("_")) snakeToDash(s) else camelToDash(s)
        		
        // ======================================================
        // Methods to get redefinitions, enumerations, flags, and records
        // ======================================================
        
        def getAcl2Redef(s: TpmStructure): String = {
            intro(s) + "(defn " + snakeToDash(s.name) + "-p (x)\n  (" + acl2Predicate(s.typedef) + " x))\n"
        }

        def getAcl2Enum(s: TpmStructure): String = {
            val nameDescPairs: List[(String, String)] = s.values.map { v => (acl2Symbol(v.name), descAbbrev(v.description)) }
            val maxLen = nameDescPairs.map(p => p._1.length()).max
            val strs = nameDescPairs.map(p => p._1 + spaces(p._1, maxLen) + " ;; " + p._2)
            val str = strs.mkString("  (", "\n   ", "\n  ))\n")
            intro(s) + "(cutil::defenum " + snakeToDash(s.name) + "-p\n" + str
        }

        def getAcl2Flag(s: TpmStructure): String = {
            val nameDescPairs: List[(String, String)] = s.values.map { v => (snakeToDash(v.name), descAbbrev(v.description)) }
            val maxLen = nameDescPairs.map(p => p._1.length()).max
            val strs = nameDescPairs.map(p => "(" + p._1 + " booleanp)" + spaces(p._1, maxLen) + " ;; " + p._2)
            val str = strs.mkString("  (", "\n   ", "\n  ))\n")
            intro(s) + "(cutil::defaggregate " + snakeToDash(s.name) + "\n" + str
        }

        def getAcl2Record(s: TpmStructure): String = {
            val nameTypeDescPairs: List[(String, String)] = s.fields.map { f => (fieldToDash(f.name) + " " + acl2Predicate(f.typeName), descAbbrev(f.description)) }
            val maxLen = nameTypeDescPairs.map(p => p._1.length()).max
            val strs = nameTypeDescPairs.map(p => "(" + p._1 + ")" + spaces(p._1, maxLen) + " ;; " + p._2)
            val str = strs.mkString("  (", "\n   ", "\n  ))\n")
            intro(s) + "(cutil::defaggregate " + snakeToDash(s.name) + "\n" + str
        }

        // ======================================================
        // Definitions are finished; main method body
        // ======================================================        
        
        val tpmStructuresXml = xml.XML.loadFile(TPMStructuresXMLFile)
        val structures: List[TpmStructure] = (tpmStructuresXml \ "structure").map(TpmStructure.fromXML(_)).toList

        val strataArray = tpmxml.util.DependencySorter.sortStructures(structures)

        val sb = new StringBuffer

        val primitiveTypesFile = scala.io.Source.fromFile(PrimitiveTypesACL2File)
        val primitiveTypesString = primitiveTypesFile.mkString
        primitiveTypesFile.close()

        sb.append(primitiveTypesString)

        for (i <- 0 to (strataArray.length - 1)) {
            val stratum = strataArray(i)

            val (recordStructures, nonRecordStructures) = stratum.partition(s => s.fields.nonEmpty)
            val (redefStructures, enumAndFlagStructures) = nonRecordStructures.partition(s => s.values.isEmpty)
            val (flagStructures, enumStructures) = enumAndFlagStructures.partition(s => s.valuesKind == "bit")

            val acl2Records = recordStructures.map(s => getAcl2Record(s)).mkString("\n")
            val acl2Enums = enumStructures.map(s => getAcl2Enum(s)).mkString("\n")
            val acl2Flags = flagStructures.map(s => getAcl2Flag(s)).mkString("\n")
            val acl2Redefs = redefStructures.map(s => getAcl2Redef(s)).mkString("\n")

            if (acl2Redefs != "") sb.append(header("Level " + i + " Wrappers") + acl2Redefs)
            if (acl2Flags != "") sb.append(header("Level " + i + " Flags") + acl2Flags)
            if (acl2Enums != "") sb.append(header("Level " + i + " Enumerations") + acl2Enums)
            if (acl2Records != "") sb.append(header("Level " + i + " Records") + acl2Records)
            
            if (i == 0) sb.append(pcrAndDigestLists)
        }

        val out = new java.io.FileWriter(TCGStructuresACL2File)
        out.write(sb.toString)
        out.close
    }
}
