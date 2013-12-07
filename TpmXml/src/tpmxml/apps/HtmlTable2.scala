package tpmxml.apps

import tpmxml.data._
import collection._

object HtmlTable2 {

    case class Slice(val slice: List[TpmParameter], val error: String)

    def main(args: Array[String]) {

        // ======================================================
        // Files
        // ====================================================== 

        val TPMStructuresXMLFile = "resources/tpm-structures-2.xml"
        val TPMCommandsXMLFile = "resources/tpm-commands-2.xml"
        val TPMStructuresHTMLFile = "resources/tpm-structures-2.html"

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
        // Definitions that restrict displayed parameters
        // ======================================================

        def inParamSlice(params: List[TpmParameter]): Slice = {
            val paramsLength = params.length

            if (paramsLength < 3) {
                Slice(params, "IN_PRE_ERROR")
            } else {
                params.head.description match {
                    case "TPM_TAG_RQU_COMMAND" => Slice(params.drop(3), "IN_SUCCESS")
                    case "TPM_TAG_RQU_AUTH1_COMMAND" =>
                        if (params.length < 8)
                            Slice(params, "IN_AUTH_ERROR")
                        else
                            Slice(params.drop(3).dropRight(5), "IN_SUCCESS")
                    case "TPM_TAG_RQU_AUTH2_COMMAND" =>
                        if (params.length < 13)
                            Slice(params, "IN_AUTH_ERROR")
                        else
                            Slice(params.drop(3).dropRight(10), "IN_SUCCESS")
                    case _ => Slice(params, "IN_PRE_ERROR")
                }
            }
        }

        def outParamSlice(params: List[TpmParameter]): Slice = {
            val paramsLength = params.length

            if (paramsLength < 4) {
                Slice(params, "OUT_PRE_ERROR")
            } else {
                params.head.description match {
                    case "TPM_TAG_RSP_COMMAND" => Slice(params.drop(4), "OUT_SUCCESS")
                    case "TPM_TAG_RSP_AUTH1_COMMAND" =>
                        if (params.length < 8)
                            Slice(params, "OUT_AUTH_ERROR")
                        else
                            Slice(params.drop(4).dropRight(4), "OUT_SUCCESS")
                    case "TPM_TAG_RSP_AUTH2_COMMAND" =>
                        if (params.length < 12)
                            Slice(params, "OUT_AUTH_ERROR")
                        else
                            Slice(params.drop(4).dropRight(8), "OUT_SUCCESS")
                    case _ => Slice(params, "OUT_PRE_ERROR")
                }
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
                "\t\t<td>" + crossRefList(s.fields.map(_.typeName).toSet) + "</td>\n" +
                "\t\t<td>" + (if (fieldOf.contains(s.name)) crossRefList(fieldOf(s.name)) else "") + "</td>\n" +
                "\t\t<td>" + (if (inParamOf.contains(s.name)) crossRefList(inParamOf(s.name)) else "") + "</td>\n" +
                "\t\t<td>" + (if (outParamOf.contains(s.name)) crossRefList(outParamOf(s.name)) else "") + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        def getValueTableRow(s: TpmStructure): String = {
            val result = "\t<tr valign=\"top\">\n" +
                "\t\t<td>" + s.section + "</td>\n" +
                "\t\t<td><a name=\"" + s.name + "\" id=\"" + s.name + "\">" + // HTML anchor
                "</a>" + s.name + "</td>\n" +
                "\t\t<td>" + (if (s.values.isEmpty) " " else crossRefList(s.values.map(_.name).toSet)) + "</td>\n" +
                "\t\t<td>" + (if (fieldOf.contains(s.name)) crossRefList(fieldOf(s.name)) else "") + "</td>\n" +
                "\t\t<td>" + (if (inParamOf.contains(s.name)) crossRefList(inParamOf(s.name)) else "") + "</td>\n" +
                "\t\t<td>" + (if (outParamOf.contains(s.name)) crossRefList(outParamOf(s.name)) else "") + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        def getCommandTableRow(c: TpmCommand): String = {
            val inSlice = inParamSlice(c.inParams)
            val outSlice = outParamSlice(c.outParams)
            val result = "\t<tr valign=\"top\">\n" +
                "\t\t<td>" + c.section + "</td>\n" +
                "\t\t<td><a name=\"" + c.name + "\" id=\"" + c.name + "\">" + // HTML anchor
                "</a>" + c.name + "</td>\n" +
                "\t\t<td><div align=\"center\">" + authDataNum(c) + "</div></td>\n" +
                "\t\t<td>" + (if (inSlice.slice.nonEmpty) crossRefList(inSlice.slice.map(_.typeName).toSet) else "") + "</td>\n" +
                "\t\t<td>" + (if (outSlice.slice.nonEmpty) crossRefList(outSlice.slice.map(_.typeName).toSet) else "") + "</td>\n" +
                "\t</tr>\n"
            return result
        }

        def authDataNum(c: TpmCommand): String = {
            val params = c.inParams
            val paramsLength = params.length

            if (params.isEmpty) {
                "No params"
            } else {
                params.head.description match {
                    case "TPM_TAG_RQU_COMMAND" => "0"
                    case "TPM_TAG_RQU_AUTH1_COMMAND" => "1"
                    case "TPM_TAG_RQU_AUTH2_COMMAND" => "2"
                    case _ => "Error"
                }
            }
        }

        def crossRefList(s: Set[String]): String = {
            val linkedSet = s.map(getHyperlinkedName(_))
            linkedSet.mkString("<ul>\n\t\t\t<li>", "</li>\n\t\t\t<li>", "</li>\n</ul>")
        }

        // ======================================================
        // Load XML files and populate maps
        // ======================================================

        /* Load the XML files */
        val tpmStructuresXml = xml.XML.loadFile(TPMStructuresXMLFile)
        val tpmCommandsXml = xml.XML.loadFile(TPMCommandsXMLFile)

        /* Transfer XML data into objects */
        val structures: List[TpmStructure] = (tpmStructuresXml \ "structure").map(TpmStructure.fromXML(_)).toList
        val commands: List[TpmCommand] = (tpmCommandsXml \ "command").map(TpmCommand.fromXML(_)).toList

        /* Map structure/command names to sections in the specification and assigned to 'section' variable. */
        section = structures.map(s => (s.name, s.section)).toMap ++ commands.map(c => (c.name, c.section)).toMap

        /* Populate fieldOf, inParamOf, and outParamOf multi-maps */
        for (s <- structures; f <- s.fields) fieldOf.addBinding(f.typeName, s.name)
        for (c <- commands; p <- inParamSlice(c.inParams).slice) inParamOf.addBinding(p.typeName, c.name)
        for (c <- commands; p <- outParamSlice(c.outParams).slice) outParamOf.addBinding(p.typeName, c.name)

        // ======================================================
        // Create HTML
        // ======================================================        

        /* Create the structure table */
        val structureTableRows: List[String] = structures.filter(_.fields.nonEmpty).map(getStructureTableRow(_))
        val structureLabels = List("Sec", "Structure", "Fields", "Field of:", "In-Param of:", "Out-Param of:")
        val structureTable = tableHeader("Structures", structureLabels) + structureTableRows.mkString + tableFooter

        /* Create the value table */
        val valueTableRows: List[String] = structures.filter(_.fields.isEmpty).map(getValueTableRow(_))
        val valueLabels = List("Sec", "Structure", "Values", "Field of:", "In-Param of:", "Out-Param of:")
        val valueTable = tableHeader("Values", valueLabels) + valueTableRows.mkString + tableFooter

        /* Create the command table */
        val commandTableRows: List[String] = commands.map(getCommandTableRow(_))
        val commandLabels = List("Sec", "Command", "Auth Blocks", "In-Params", "Out-Params")
        val commandTable = tableHeader("Commands", commandLabels) + commandTableRows.mkString + tableFooter

        /* Write to HTML file */
        val out = new java.io.FileWriter(TPMStructuresHTMLFile)
        out.write(pageHeader + structureTable + valueTable + commandTable + pageFooter)
        out.close
    }
}