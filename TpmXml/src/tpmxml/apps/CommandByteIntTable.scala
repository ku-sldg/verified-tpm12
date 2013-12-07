package tpmxml.apps

import tpmxml.data._
import collection._

object CommandByteIntTable {

    def main(args: Array[String]) {

        case class TpmParam(
            section: String,
            commandName: String,
            paramKind: String, // "in" or "out"
            paramName: String,
            paramType: String,
            paramDesc: String)

        // ======================================================
        // Files
        // ====================================================== 

        val TPMCommandsXMLFile = "resources/tpm-commands.xml"
        val TPMStructuresHTMLFile = "resources/tpm-command-byte-int.html"

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

        def getTableRow(p: TpmParam): String = {
            val result = "\t<tr valign=\"top\">\n" +
                "\t\t<td>" + p.section + "</td>\n" +
                "\t\t<td>" + p.commandName + "</td>\n" +
                "\t\t<td>" + p.paramKind + "</td>\n" +
                "\t\t<td>" + p.paramName + "</td>\n" +
                "\t\t<td>" + p.paramType + "</td>\n" +
                "\t\t<td>" + p.paramDesc + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        // ======================================================
        // Load XML files and populate maps
        // ======================================================

        /* Define helpful definitions */
        def getTpmParamList(c: TpmCommand): List[TpmParam] = {
            c.inParams.filter(p => byteOrIntFilter(p)).map(p => makeTpmParam(c, p, "in")) :::
                c.outParams.filter(p => byteOrIntFilter(p)).map(p => makeTpmParam(c, p, "out"))
        }

        def byteOrIntFilter(p: TpmParameter) = {
            p.name != "paramSize" && (p.typeName.startsWith("BYTE") || p.typeName.startsWith("UINT"))
        }

        def makeTpmParam(c: TpmCommand, p: TpmParameter, k: String) = {
            TpmParam(c.section, c.name, k, p.name, p.typeName, p.description)
        }

        /* Load the XML file */
        val tpmCommandsXml = xml.XML.loadFile(TPMCommandsXMLFile)

        /* Transfer XML data into objects */
        val commands: List[TpmCommand] = (tpmCommandsXml \ "command").map(TpmCommand.fromXML(_)).toList

        /* Flatten List[TpmCommand] to List[TpmParam] for incoming (see case class above) */
        val byteIntParams = commands.flatMap(c => getTpmParamList(c))

        // ======================================================
        // Create HTML
        // ======================================================        

        /* Create the command byte-int table */
        val tableRows: List[String] = byteIntParams.map(getTableRow(_))
        val labels = List("Sec", "Command", "In/out", "Param Name", "Param Type", "Description")
        val table = tableHeader("Command Bytes and Int Parameters", labels) + tableRows.mkString + tableFooter

        /* Write to HTML file */
        val out = new java.io.FileWriter(TPMStructuresHTMLFile)
        out.write(pageHeader + table + pageFooter)
        out.close
    }
}