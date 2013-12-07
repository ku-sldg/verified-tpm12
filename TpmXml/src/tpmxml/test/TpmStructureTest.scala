package tpmxml.test

import tpmxml.data._

object TpmStructureTest {

    def main(args: Array[String]) {
        
        val structname = "TPM_SYMMETRIC_KEY"
        
        def descAbbrev(desc: String): String =
            if (desc.length > 20) {
                desc.take(20) + "..."
            } else {
                desc
            }
        
        def flagOpt(flag: String): String =
            if (flag != "") {
                " @" + flag
            } else {
                ""
            }
            
        val tpmStructuresXml = xml.XML.loadFile("resources/tpm-structures.xml")
        val structures: List[TpmStructure] = (tpmStructuresXml \ "structure").map(TpmStructure.fromXML(_)).toList
        val myStructure = structures.find(_.name == structname)
        myStructure match {
            case Some(s) => {
            	println(s.section + " " + s.name + (if (s.typedef != "") {" ( " + s.typedef + " )"} else {""}) + (if (s.valuesKind != "") {" [" + s.valuesKind + "]"} else {""}))
            	s.values.foreach(v => println("  - " + v.name + ": " + v.value + " // " + descAbbrev(v.description)))
            	s.fields.foreach(f => println("  - " + f.name + ": " + f.typeName + flagOpt(f.flag) + " // " + descAbbrev(f.description)))
            }
            case None => println("No match")
        }
    }
}