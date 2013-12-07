package tpmxml.data

case class TpmCommand(
    val section: String,
    val name: String,
    val inParams: List[TpmParameter],
    val outParams: List[TpmParameter]) {

    override def toString = name + " (" + section + ")"

    def toXML =
        <command>
            <name>{ name }</name>
            <section>{ section }</section>
            {
                if (inParams.isEmpty) xml.NodeSeq.Empty
                else <incomingParameters>{ inParams.map(p => p.toXML).toSeq }</incomingParameters>
            }
            {
                if (outParams.isEmpty) xml.NodeSeq.Empty
                else <outgoingParameters>{ outParams.map(f => f.toXML).toSeq }</outgoingParameters>
            }
        </command>
}

object TpmCommand {

    def fromXML(node: scala.xml.Node) = {
        val inParamNode = (node \ "incomingParameters")
        val outParamNode = (node \ "outgoingParameters")
        TpmCommand(
            name = (node \ "name").text,
            section = (node \ "section").text,
            inParams = (inParamNode \ "parameter").map(p => TpmParameter.fromXML(p)).toList,
            outParams = (outParamNode \ "parameter").map(p => TpmParameter.fromXML(p)).toList)
    }
}
