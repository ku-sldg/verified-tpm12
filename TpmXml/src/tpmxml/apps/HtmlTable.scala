package tpmxml.apps

import tpmxml.data._
import collection._

object HtmlTable {

    def main(args: Array[String]) {

        // ======================================================
        // Files
        // ====================================================== 
       
        val TpmStructuresXMLFile = "resources/tpm-structures.xml"
        val TpmCommandsXMLFile = "resources/tpm-commands.xml"
        val TpmStructuresHTMLFile = "resources/tpm-structures.html"
        
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
        // Variables and mutable values
        // ======================================================

        /* section map will be reset to a non-empty, immutable object once XML data is read and put into objects. */
        var section: Map[String, String] = Map.empty

        /*
         * In each map, the key is the structure of interest, and the value is the set of structures
         * or commands where the key can be found. 
         */
        val fieldOf = new mutable.HashMap[String, mutable.Set[String]] with mutable.MultiMap[String, String] // mutable
        val inParamOf = new mutable.HashMap[String, mutable.Set[String]] with mutable.MultiMap[String, String] // mutable
        val outParamOf = new mutable.HashMap[String, mutable.Set[String]] with mutable.MultiMap[String, String] // mutable

        // ======================================================
        // Helper definitions
        // ======================================================

        def tableHeader(title: String, labels: List[String]) = {
            val headerCells = labels.map(label => "<th scope=\"col\">" + label + "</th>")
            val headerRow = headerCells.mkString("\t<tr>\n\t\t", "\n\t\t", "\n\t</tr>\n")
            "<h1>" + title + "</h1>\n" + "<table border=\"1\">\n" + headerRow
        }

        /* The hyper-linked name depends on section map and is used below, therefore we place the function here. */
        def getHyperlinkedName(name: String): String = {
            if (section.contains(name)) {
                "<a href=\"#" + name + "\">" + name + "</a> (" + section(name) + ")"
            } else {
                name
            }
        }

        // ======================================================
        // Definitions that create table rows
        // ======================================================

        def getStructureTableRow(s: TpmStructure): String = {
            val result = "\t<tr valign=\"top\">\n" +
                "\t\t<td>" + s.section + "</td>\n" +
                "\t\t<td><a name=\"" + s.name + "\" id=\"" + s.name + "\">" + // HTML anchor
                "</a>" + s.name + "</td>\n" +
                "\t\t<td>" + (if (s.fields.isEmpty) " = " + s.typedef else crossRefList(s.fields.map(_.typeName).toSet)) + "</td>\n" +
                "\t\t<td>" + (if (fieldOf.contains(s.name)) crossRefList(fieldOf(s.name)) else "") + "</td>\n" +
                "\t\t<td>" + (if (inParamOf.contains(s.name)) crossRefList(inParamOf(s.name)) else "") + "</td>\n" +
                "\t\t<td>" + (if (outParamOf.contains(s.name)) crossRefList(outParamOf(s.name)) else "") + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        def getValueTableRow(s: TpmStructure): String = {
            val result = "\t<tr valign=\"top\">\n" +
                "\t\t<td>" + s.section + "</td>\n" +
                "\t\t<td>" + s.name + "</td>\n" +
                "\t\t<td>" + crossRefList(s.values.map(_.name).toSet) + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        def getCommandTableRow(c: TpmCommand): String = {
            val result = "\t<tr valign=\"top\">\n" +
                "\t\t<td>" + c.section + "</td>\n" +
                "\t\t<td><a name=\"" + c.name + "\" id=\"" + c.name + "\">" + // HTML anchor
                "</a>" + c.name + "</td>\n" +
                "\t\t<td>" + (if (c.inParams.nonEmpty) crossRefList(c.inParams.map(_.typeName).toSet) else "") + "</td>\n" +
                "\t\t<td>" + (if (c.outParams.nonEmpty) crossRefList(c.outParams.map(_.typeName).toSet) else "") + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        def crossRefList(s: Set[String]): String = {
            val linkedSet = s.map(getHyperlinkedName(_))
            linkedSet.mkString("<ul>\n\t\t\t<li>", "</li>\n\t\t\t<li>", "</li>\n</ul>")
        }

        // ======================================================
        // Load XML files and populate maps
        // ======================================================

        /* Load the XML files */
        val tpmStructuresXml = xml.XML.loadFile(TpmStructuresXMLFile)
        val tpmCommandsXml = xml.XML.loadFile(TpmCommandsXMLFile)

        /* Transfer XML data into objects */
        val structures: List[TpmStructure] = (tpmStructuresXml \ "structure").map(TpmStructure.fromXML(_)).toList
        val commands: List[TpmCommand] = (tpmCommandsXml \ "command").map(TpmCommand.fromXML(_)).toList

        /* Map structure/command names to sections in the specification and assigned to 'section' variable. */
        section = structures.map(s => (s.name, s.section)).toMap ++ commands.map(c => (c.name, c.section)).toMap

        /* Populate fieldOf, inParamOf, and outParamOf multi-maps */
        for (s <- structures; f <- s.fields) fieldOf.addBinding(f.typeName, s.name)
        for (c <- commands; p <- c.inParams) inParamOf.addBinding(p.typeName, c.name)
        for (c <- commands; p <- c.outParams) outParamOf.addBinding(p.typeName, c.name)

        // ======================================================
        // Create HTML
        // ======================================================        

        /* Create the structure table */
        val structureTableRows: List[String] = structures.map(getStructureTableRow(_))
        val structureLabels = List("Sec", "Structure", "Fields", "Field of:", "In-Param of:", "Out-Param of:")
        val structureTable = tableHeader("Types", structureLabels) + structureTableRows.mkString + tableFooter

        /* Create the value table */
        val valueTableRows: List[String] = structures.filter(_.values.nonEmpty).map(getValueTableRow(_))
        val valueLabels = List("Sec", "Structure", "Values")
        val valueTable = tableHeader("Enumerations", valueLabels) + valueTableRows.mkString + tableFooter

        /* Create the command table */
        val commandTableRows: List[String] = commands.map(getCommandTableRow(_))
        val commandLabels = List("Sec", "Command", "In-Params", "Out-Params")
        val commandTable = tableHeader("Operations", commandLabels) + commandTableRows.mkString + tableFooter

        /* Write to HTML file */
        val out = new java.io.FileWriter(TpmStructuresHTMLFile)
        out.write(pageHeader + structureTable + valueTable + commandTable + pageFooter)
        out.close
    }
}