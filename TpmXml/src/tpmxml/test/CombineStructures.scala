package tpmxml.test

import tpmxml.data.TpmStructure

object CombineStructures {

    // ======================================================
    // Files
    // ====================================================== 

    val structuresFile = "resources/tpm-structures-orig.xml"
    val addFile = "resources/tpm-structures-add.xml"
    val newStructuresFile = "resources/tpm-structures-2.xml"

    // ======================================================
    // Main definition
    // ====================================================== 

    def main(args: Array[String]) {

        def addDesc(s: TpmStructure, addStructs: List[TpmStructure]): TpmStructure = {
            val descStruct = addStructs.find(_.name == s.name)
            descStruct match {
                case Some(x) => s.copy(description = x.description)
                case None => s
            }
        }

        val structuresOrig = xml.XML.loadFile(structuresFile)
        val structuresAdd = xml.XML.loadFile(addFile)

        val origStructures: List[TpmStructure] = (structuresOrig \ "structure").map(TpmStructure.fromXML(_)).toList
        val addStructures: List[TpmStructure] = (structuresAdd \ "structure").map(TpmStructure.fromXML(_)).toList

        println("origStructures length = " + origStructures.length)
        println("addStructures length = " + addStructures.length)

        //DEBUG: find structures with duplicate names
        val (seen, dups) = origStructures.foldLeft(Set[String](), Set[String]()) {
            (r, c) =>
                val name = c.name
                if (r._1.contains(name)) {
                    (r._1, r._2 + name)
                } else {
                    (r._1 + name, r._2)
                }
        }
        println(dups)
        // TPM_STANY_DATA is duplicated because 22.7 extends it with new fields

        // DEBUG:
        val found = origStructures.find(_.name == "TPM_CHANGEAUTH_VALIDATE")
        val num = found match {
            case Some(x) => x.fields.length
            case None => -1
        }
        println("TPM_CHANGEAUTH_VALIDATE fields = " + num)

        val origNames = origStructures.map(_.name).toSet
        val addNames = addStructures.map(_.name).toSet

        println("origNames size = " + origNames.size)
        println("addNames size = " + addNames.size)

        val uniqueAddNames = addNames.diff(origNames)
        val (uniqueAddStructures, commonAddStructures) = addStructures.partition(s => uniqueAddNames.contains(s.name))

        println("uniqueAddNames size = " + uniqueAddNames.size)
        println("uniqueAddStructures size = " + uniqueAddStructures.size)
        println("commonAddStructures size = " + commonAddStructures.size)

        val enhancedOrigStructures: List[TpmStructure] = origStructures.map(s => (addDesc(s, commonAddStructures)))
        val enhUnifiedStructures: List[TpmStructure] = (uniqueAddStructures.toList) ::: enhancedOrigStructures

        println("enhancedOrigStructures length = " + enhancedOrigStructures.length)
        println("enhUnifiedStructures length = " + enhUnifiedStructures.length)

        // DEBUG:
        val found2 = enhUnifiedStructures.find(_.name == "TPM_CHANGEAUTH_VALIDATE")
        val num2 = found match {
            case Some(x) => x.fields.length
            case None => -1
        }
        println("TPM_CHANGEAUTH_VALIDATE fields = " + num2)

        val nodeSeq = enhUnifiedStructures.map(s => s.toXML).toSeq

        val node = <structures> { nodeSeq } </structures>
        
        // ======================================================
        // Output the XML file in pretty printed format
        // ======================================================
        
        /*
         * Definition from gerferra in response to Stack Overflow question
         * @see http://stackoverflow.com/questions/3364627/how-to-produce-nicely-formatted-xml-in-scala
         */
        
        val Encoding = "UTF-8"

        def save(node: scala.xml.Node, fileName: String) = {

            val pp = new scala.xml.PrettyPrinter(80, 4)
            val fos = new java.io.FileOutputStream(fileName)
            val writer = java.nio.channels.Channels.newWriter(fos.getChannel(), Encoding)

            try {
                writer.write("<?xml version='1.0' encoding='" + Encoding + "'?>\n")
                writer.write(pp.format(node))
            } finally {
                writer.close()
            }

            fileName
        }
        
        save(node, newStructuresFile)
        
//        // The following pretty printed to a file, but some characters were not understood by my text editor
//        val pp = new scala.xml.PrettyPrinter(80, 4)
//        val sb = new StringBuilder()
//        pp.format(node, sb)
//        
//        val out = new java.io.FileWriter(newStructuresFile)
//        out.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" + sb.toString)
//        out.close
        
//        // The following is safer but does not pretty-print the output
//        scala.xml.XML.saveFull(newStructuresFile, node, "UTF8", true, null)
    }
}