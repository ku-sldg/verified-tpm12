package tpmxml.data

case class TpmParameter(
    val name: String,
    val typeName: String,
    val description: String,
    val paramNum: String,
    val paramSize: String,
    val hmacNum: String,
    val hmacSize: String) {

    override def toString = name + ": " + typeName

    def toXML =
        <parameter>
            <name>{ name }</name>
            <typename>{ typeName }</typename>
            <description>{ description }</description>
            <paramNum>{ paramNum }</paramNum>
            <paramSize>{ paramSize }</paramSize>
            <hmacNum>{ hmacNum }</hmacNum>
            <hmacSize>{ hmacSize }</hmacSize>
        </parameter>
}

object TpmParameter {

    def fromXML(node: scala.xml.Node) =
        TpmParameter(
            name = (node \ "name").text,
            typeName = (node \ "type").text,
            description = (node \ "description").text,
            paramNum = (node \ "paramNum").text,
            paramSize = (node \ "paramSize").text,
            hmacNum = (node \ "hmacNum").text,
            hmacSize = (node \ "hmacSize").text)
}        