package tpmxml.data

case class TpmValue(
    val name: String,
    val value: String,
    val description: String) {

    override def toString = name

    def toXML =
        <value>
            <name>{ name }</name>
            <numValue>{ value }</numValue>
            <description>{ description }</description>
        </value>
}

object TpmValue {

    def fromXML(node: scala.xml.Node) =
        TpmValue(
            name = (node \ "name").text,
            value = (node \ "numValue").text,
            description = (node \ "description").text)
}
