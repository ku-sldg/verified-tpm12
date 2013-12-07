package tpmxml.apps

import tpmxml.data._

object ACL2Structures {

    def main(args: Array[String]) {
        
    	def acl2Name(tcgName: String): String = {
    	    // assumes names in camel case
    		val splitter = """(?<!(^|[A-Z]))(?=[A-Z])|(?<!^)(?=[A-Z][a-z])"""
    	    tcgName.split(splitter).mkString("-").toLowerCase()
    	}
    	
    	def acl2Type(tcgType: String): String = {
    	    // assumes names in upper case separated by underscores
    	    tcgType.toLowerCase().replace('_', '-')
    	}

    	def typeLemma(structName: String, fieldName: String, fieldType: String): String = {
    	    "(" + acl2Type(fieldType) + "-p-of-" + acl2Type(structName) + "->" + acl2Name(fieldName) + "\n      " +
    	    "(" + acl2Type(fieldType) + " " + acl2Name(fieldName) + "))"
    	}
    	
    	def getAcl2Aggregate(s: TpmStructure): String = {
    	    // assume !s.fields.isEmpty
    	    val acl2Fields: List[String] = s.fields.map(f => acl2Name(f.name))
    	    val acl2Lemmas: List[String] = s.fields.map(f => typeLemma(s.name, f.name, f.typeName))
    	    val acl2FieldString = acl2Fields.mkString("  ( ", "\n    ", ")\n")
    	    val acl2LemmaString = acl2Lemmas.mkString("  ( ", "\n    ", ")\n")
    	    "(cutil::defaggregate " + acl2Type(s.name) + "\n" + acl2FieldString +
    	    ":require\n" + acl2LemmaString
    	}
    	
        val tpmStructuresXml = xml.XML.loadFile("resources/tpm-structures.xml")
        val structures: List[TpmStructure] = (tpmStructuresXml \ "structure").map(TpmStructure.fromXML(_)).toList
        
        val acl2Aggregates: List[String] = structures.filter(s => !s.fields.isEmpty).map(s => getAcl2Aggregate(s))
        
        val header = "(in-package \"ACL2\")\n\n" +
        		"(include-book \"cutil/defaggregate\" :dir :system)\n" +
        		"(include-book \"cutil/deflist\" :dir :system)\n\n" +
        		"(program)\n\n"

	    val out = new java.io.FileWriter("resources/tcg-structures.lisp")
        out.write(header + acl2Aggregates.mkString("\n"))
        out.close
    }
}