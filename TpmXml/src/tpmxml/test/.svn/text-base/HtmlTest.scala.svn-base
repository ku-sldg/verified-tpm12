package tpmxml.test

import tpmxml.data._

object HtmlTest {
    
    val header = "<html>\n" +
    "<head>\n" +
    "<title>TPM Structures</title>\n" +
    "<style type=\"text/css\">\n" +
    "<!--\n" + 
    "body,td,th {\n" +
    "\tfont-family: Verdana, Arial, Helvetica, sans-serif;\n" +
	"\tfont-size: small;\n" +
	"}\n" +
	"-->\n" +
	"</style>\n" +
	"</head>\n" +
	"<body>\n" +
	"<h1>Types</h1>\n" +
	"<table border=\"1\">\n" +
	"\t<tr>\n" +
	"\t\t<th scope=\"col\">Sec</th>\n" +
	"\t\t<th scope=\"col\">Type</th>\n" +
	"\t\t<th scope=\"col\">Fields</th>\n" +
	"\t\t<th scope=\"col\">Fields of</th>\n" +
	"</tr>\n"
	
    
	val footer = "</table>\n</body>\n</html>"
	
	def main(args: Array[String]) {
        val tpmStructuresXml = xml.XML.loadFile("resources/tpm-structures.xml")
        val structures: List[TpmStructure] = (tpmStructuresXml \\ "structure").map(TpmStructure.fromXML(_)).toList
	    val tableRows: List[String] = structures.map(getTableRow(_, structures))
	    val tableBody = tableRows.mkString
	    val out = new java.io.FileWriter("resources/tpm-structures.html")
        out.write(header + tableBody + footer)
        out.close
	}
    
    def getTableRow(structure: TpmStructure, structures: List[TpmStructure]): String = {
        val result = "\t<tr>\n" +
        	"\t\t<td>" + structure.section + "</td>\n" +
        	"\t\t<td>" + structure.name + "</td>\n" +
        	"\t\t<td>" + getFieldSetAsHtmlList(structure) + "</td>\n" +
        	"\t\t<td>" + getFieldOfSetAsHtmlList(structure, structures) + "</td>\n" +
        	"\t</tr>\n"
        return result
    }
    
    def getFieldSetAsHtmlList(s: TpmStructure): String = {
        if (s.typedef != "") {
            "=" + s.typedef
        } else if (s.fields.isEmpty) {
            ""
        } else {
            val fieldTypeSet: Set[String] = s.fields.map(_.typeName).toSet
            fieldTypeSet.mkString("<ul>\n\t\t\t<li>", "</li>\n\t\t\t<li>", "</li>\n</ul>")
        }
    }
    
    def getFieldOfSetAsHtmlList(s: TpmStructure, ss: List[TpmStructure]): String = {
        val relevantStructures = ss.filter(containsFieldWithTypename(_, s.name))
        val relevantTypenameSet = relevantStructures.map(_.name).toSet
        if (relevantTypenameSet.isEmpty) {
            ""
        } else {
        	relevantTypenameSet.mkString("<ul>\n\t\t\t<li>", "</li>\n\t\t\t<li>", "</li>\n</ul>")
        }
    }
    
    def containsFieldWithTypename(s: TpmStructure, typeName: String): Boolean = {
        val result = s.fields.find(_.typeName == typeName)
        result match {
            case Some(x) => true
            case None => false
        }
    }
}
