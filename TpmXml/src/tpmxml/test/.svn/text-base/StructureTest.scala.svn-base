package tpmxml.test

object StructureTest {

    def main(args: Array[String]) {
        println("Hello, world!")
        val structures = xml.XML.loadFile("resources/tpm-structures.xml")
        val structureSeq = structures \ "structure"
        println("number of stuctures = " + structureSeq.length)
        val myStructure = structureSeq.find(s => (s \ "name").text == "TPM_SYMMETRIC_KEY")
        myStructure match {
            case Some(s) => prettyPrint(s)
            case None => println("Structure not found")
        }
    }
    
    def prettyPrint(structure: xml.Node) {
        def prettyPrintParam(param: xml.Node) {
            println("\t" + (param \ "name").text + ": " + (param \ "type").text)
        }
        println((structure \ "section").text + " " + (structure \ "name").text)
        val params = structure \\ "parameter"
        val body = params.foreach(p => prettyPrintParam(p))
    }
}
