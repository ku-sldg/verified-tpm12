package tpmxml.data

case class TpmField(
    val name: String,
    val typeName: String,
    val flag: String,
    val description: String) {

    override def toString = name + ": " + typeName

    def toXML =
        <parameter>
            <name>{ name }</name>
            <type>{ typeName }</type>
            <flag>{ flag }</flag>
            <description>{ description }</description>
        </parameter>
}

object TpmField {

    def fromXML(node: scala.xml.Node) =
        TpmField(
            name = (node \ "name").text,
            typeName = (node \ "type").text,
            flag = (node \ "flag").text,
            description = (node \ "description").text)
}