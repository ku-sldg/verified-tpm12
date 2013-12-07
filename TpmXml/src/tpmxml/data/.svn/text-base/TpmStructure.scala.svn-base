package tpmxml.data

case class TpmStructure(
    val section: String,
    val name: String,
    val typedef: String,
    val description: String,
    val restrictions: String, 	// "none", "internal", "external"
    val traceability: String, 	// "explicit", "implied", "something else..."
    val valuesKind: String,		// "none" (values.isEmpty), "numeric", "bit"
    val values: List[TpmValue], // if nonEmpty, then fields.isEmpty and typedef != "struct"
    val fields: List[TpmField] 	// if nonEmpty, then values.isEmpty and typedef = "struct"
    ) {

    // Note: "explicit" traceability means that the structure was:
    //     (1) explicitly defined as a "struct" in TCG Spec Part 2, OR
    //     (2) explicitly given as a redefinition in TCG Spec Part 2 (Table 2.2.3, TPM_DIGEST, TPM_NONCE, or TPM_AUTHDATA)

    override def toString = name + " (" + section + ")"

    def toXML =
        <structure>
            <name>{ name }</name>
            <section>{ section }</section>
            <typedef>{ typedef }</typedef>
            <description>{ description }</description>
            <restrictions>{ restrictions }</restrictions>
            <traceability>{ traceability }</traceability>
            {
                if (values.isEmpty) xml.NodeSeq.Empty
                else <values>{ values.map(v => v.toXML).toSeq }</values> % xml.Attribute("kind", xml.Text(valuesKind), xml.Null)
            }
            {
                if (fields.isEmpty) xml.NodeSeq.Empty
                else <parameters>{ fields.map(f => f.toXML).toSeq }</parameters>
            }
        </structure>
}

object TpmStructure {

    def fromXML(node: scala.xml.Node): TpmStructure = {
        val valuesNode = (node \ "values")
        val fieldsNode = (node \ "parameters")
        TpmStructure(
            name = (node \ "name").text,
            section = (node \ "section").text,
            typedef = (node \ "typedef").text,
            description = (node \ "description").text,
            restrictions = (node \ "restrictions").text,
            traceability = (node \ "traceability").text,
            valuesKind = (valuesNode \ "@kind").text,
            values = (valuesNode \ "value").map(v => TpmValue.fromXML(v)).toList,
            fields = (fieldsNode \ "parameter").map(f => TpmField.fromXML(f)).toList)
    }
}