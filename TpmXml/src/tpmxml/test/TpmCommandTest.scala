package tpmxml.test

import tpmxml.data._

object TpmCommandTest {

    // ==========================================================
    // Files
    // ==========================================================
    
    val TPMCommandsXMLFile = "resources/tpm-commands.xml"
        
    // ==========================================================
    // Inner classes
    // ==========================================================
    
    case class Slice(val slice: List[TpmParameter], val error: String)
    
    // ==========================================================
    // Main method
    // ==========================================================

    def main(args: Array[String]) {
        
        val command = "TPM_MakeIdentity"
        
        def descAbbrev(desc: String): String =
            if (desc.length > 20) {
                desc.take(20) + "..."
            } else {
                desc
            }
        
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
        
        val tpmCommandsXml = xml.XML.loadFile(TPMCommandsXMLFile)
        val commands: List[TpmCommand] = (tpmCommandsXml \ "command").map(TpmCommand.fromXML(_)).toList
        val myCommand = commands.find(_.name == command)
        myCommand match {
            case Some(s) => {
            	println(s.section + " " + s.name)
            	println("Incoming Parameters")
            	val inSlice = inParamSlice(s.inParams)
            	inSlice.slice.foreach(p => println("  - " + p.name + ": " + p.typeName + " // " + descAbbrev(p.description)))
            	println("Outgoing Parameters")
            	val outSlice = outParamSlice(s.outParams)
            	outSlice.slice.foreach(p => println("  - " + p.name + ": " + p.typeName + " // " + descAbbrev(p.description)))
            }
            case None => println("No match")
        }
    }
}