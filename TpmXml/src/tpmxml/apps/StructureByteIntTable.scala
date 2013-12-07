package tpmxml.apps

import tpmxml.data._
import collection._

object StructureByteIntTable {

    def main(args: Array[String]) {

        case class TpmByteIntField(
            section: String,
            structureName: String,
            fieldName: String,
            fieldType: String,
            fieldDesc: String)

        // ======================================================
        // Files
        // ====================================================== 

        val TPMStructuresXMLFile = "resources/tpm-structures.xml"
        val TPMStructureByteIntHTMLFile = "resources/tpm-structure-byte-int.html"

        // ======================================================
        // Constants
        // ======================================================

        val styleInfo = "<style type=\"text/css\">\n<!--\nbody,td,th {\n" +
            "\tfont-family: Verdana, Arial, Helvetica, sans-serif;\n" +
            "\tfont-size: small;\n}\n-->\n</style>\n"
        val pageHeader = "<html>\n<head>\n<title>TPM Structures and Commands</title>\n" +
            styleInfo + "</head>\n<body>\n"
        val pageFooter = "</body>\n</html>"
        // Note: tableHeader depends on input; see helper definitions below
        val tableFooter = "</table>\n"

        // ======================================================
        // Helper definitions
        // ======================================================

        def tableHeader(title: String, labels: List[String]) = {
            val headerCells = labels.map(label => "<th scope=\"col\">" + label + "</th>")
            val headerRow = headerCells.mkString("\t<tr>\n\t\t", "\n\t\t", "\n\t</tr>\n")
            "<h1>" + title + "</h1>\n" + "<table border=\"1\">\n" + headerRow
        }

        // ======================================================
        // Definitions that create table rows
        // ======================================================

        def getTableRow(f: TpmByteIntField): String = {
            val result = "\t<tr valign=\"top\">\n" +
                "\t\t<td>" + f.section + "</td>\n" +
                "\t\t<td>" + f.structureName + "</td>\n" +
                "\t\t<td>" + f.fieldName + "</td>\n" +
                "\t\t<td>" + f.fieldType + "</td>\n" +
                "\t\t<td>" + f.fieldDesc + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        // ======================================================
        // Load XML files and populate maps
        // ======================================================

        /* Define helpful definitions */
        def getTpmByteIntFieldList(s: TpmStructure): List[TpmByteIntField] = {
            s.fields.filter(f => byteOrIntFilter(f)).map(f => makeTpmByteIntField(s, f))
        }

        def byteOrIntFilter(f: TpmField) = {
            f.typeName.startsWith("BYTE") || f.typeName.startsWith("UINT")
        }

        def makeTpmByteIntField(s: TpmStructure, f: TpmField) = {
            TpmByteIntField(s.section, s.name, f.name, f.typeName, f.description)
        }

        /* Load the XML file */
        val tpmStructuresXml = xml.XML.loadFile(TPMStructuresXMLFile)

        /* Transfer XML data into objects */
        val structures: List[TpmStructure] = (tpmStructuresXml \ "structure").map(TpmStructure.fromXML(_)).toList

        /* Flatten List[TpmCommand] to List[TpmParam] for incoming (see case class above) */
        val byteIntParams = structures.flatMap(s => getTpmByteIntFieldList(s))

        // ======================================================
        // Create HTML
        // ======================================================        

        /* Create the command byte-int table */
        val tableRows: List[String] = byteIntParams.map(getTableRow(_))
        val labels = List("Sec", "Structure", "Field Name", "Field Type", "Description")
        val table = tableHeader("Structure Byte and Int Parameters", labels) + tableRows.mkString + tableFooter

        /* Write to HTML file */
        val out = new java.io.FileWriter(TPMStructureByteIntHTMLFile)
        out.write(pageHeader + table + pageFooter)
        out.close
    }
}