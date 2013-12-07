package tpmxml.test

object StructureListTest {
    
	def main(args: Array[String]) {
		val structures = xml.XML.loadFile("resources/tpm-structures.xml")
        val structureSeq = structures \ "structure"
        println(structureSeq.length)
        val (structSeq, valueSeq) = structureSeq.partition(s => (s \ "parameters").text != "")
        println("# Records (" + structSeq.length + ")")
        println
        structSeq.foreach(s => println((s \ "name").text + " (" + (s \ "section").text + ")"))
        println
        println("# Values (" + valueSeq.length + ")")
        println
        valueSeq.foreach(v => println((v \ "name").text + " (" + (v \ "section").text + ")"))
	}

}