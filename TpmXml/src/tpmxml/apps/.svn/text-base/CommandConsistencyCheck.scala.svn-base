package tpmxml.apps

import tpmxml.data.TpmCommand
import tpmxml.data.TpmParameter

/*
 * Does every command have TPM_TAG tag as its first incoming parameter?
 * Does every command have UINT32 paramSize as its second incoming parameter?
 * Does every command have TPM_COMMAND_CODE ordinal as its third incoming parameter?
 *
 * If incoming tag = TPM_TAG_RQU_AUTH2_COMMAND,
 * do the last *two* blocks of parameters have the following types?
 *	 - TPM_AUTHHANDLE
 *	 - TPM_NONCE
 *	 - TPM_NONCE
 *	 - BOOL
 *	 - TPM_AUTHDATA
 *
 * Does every command have TPM_TAG tag as its first outgoing parameter?
 * Does every command have UINT32 paramSize as its second outgoing parameter?
 * Does every command have TPM_RESULT returnCode as its third outgoing parameter?
 * Does every command have TPM_COMMAND_CODE ordinal as its fourth outgoing parameter?
 *
 * If outgoing tag = TPM_TAG_RSP_AUTH2_COMMAND,
 * do the last *two* blocks of parameters have the following types?
 *	 - TPM_NONCE
 *	 - TPM_NONCE
 *	 - BOOL
 *	 - TPM_AUTHDATA
 */
object CommandConsistencyCheck {

    // ==========================================================
    // Error strings
    // ==========================================================

    val IN_TAG_NAME_ERR = ": 1st input param name is not \"tag\", but "
    val IN_TAG_TYPE_ERR = ": 1st input param type is not \"TPM_TAG\", but "
    val IN_TAG_DESC_ERR = ": 1st input param desc is not valid. Desc = "
    val IN_SIZE_NAME_ERR = ": 2st input param name is not \"paramSize\", but "
    val IN_SIZE_TYPE_ERR = ": 2st input param type is not \"UINT32\", but "
    val IN_CODE_NAME_ERR = ": 3rd input param name is not \"ordinal\", but "
    val IN_CODE_TYPE_ERR = ": 3rd input param type is not \"TPM_COMMAND_CODE\", but "
    val IN_AUTH_BLOCK_ERR = ": Input auth block does not have types List(TPM_AUTHHANDLE, TPM_NONCE, TPM_NONCE, BOOL, TPM_AUTHDATA) but "
    val IN_TOO_FEW_AUTH0_ERR = ": Too few input params for TPM_TAG_RQU_COMMAND. Required: 3 or more. Found: "
    val IN_TOO_FEW_AUTH1_ERR = ": Too few input params for TPM_TAG_RQU_AUTH1_COMMAND. Required: 8 or more. Found: "
    val IN_TOO_FEW_AUTH2_ERR = ": Too few input params for TPM_TAG_RQU_AUTH2_COMMAND. Required: 13 or more. Found: "

    val OUT_TAG_NAME_ERR = ": 1st output param name is not \"tag\", but "
    val OUT_TAG_TYPE_ERR = ": 1st output param type is not \"TPM_TAG\", but "
    val OUT_TAG_DESC_ERR = ": 1st output param desc is not valid. Desc = "
    val OUT_SIZE_NAME_ERR = ": 2st output param name is not \"paramSize\", but "
    val OUT_SIZE_TYPE_ERR = ": 2st output param type is not \"UINT32\", but "
    val OUT_RET_NAME_ERR = ": 3rd output param name is not \"returnCode\", but "
    val OUT_RET_TYPE_ERR = ": 3rd output param type is not \"TPM_RESULT\", but "        
    val OUT_CODE_NAME_ERR = ": 4th output param name is not \"ordinal\", but "
    val OUT_CODE_TYPE_ERR = ": 4th output param type is not \"TPM_COMMAND_CODE\", but "
    val OUT_AUTH_BLOCK_ERR = ": Output auth block does not have types List(TPM_NONCE, TPM_NONCE, BOOL, TPM_AUTHDATA) but "
    val OUT_TOO_FEW_AUTH0_ERR = ": Too few output params for TPM_TAG_RSP_COMMAND. Required: 4 or more. Found: "
    val OUT_TOO_FEW_AUTH1_ERR = ": Too few output params for TPM_TAG_RSP_AUTH1_COMMAND. Required: 8 or more. Found: "
    val OUT_TOO_FEW_AUTH2_ERR = ": Too few output params for TPM_TAG_RSP_AUTH2_COMMAND. Required: 12 or more. Found: "

    // ==========================================================
    // Input Files
    // ==========================================================

    val TPMStructuresXMLFile = "resources/tpm-structures-2.xml"
    val TPMCommandsXMLFile = "resources/tpm-commands-2.xml"

    // ==========================================================
    // Main method
    // ==========================================================

    def main(args: Array[String]) {

        // create structureNames: Set[String]

        val structures = xml.XML.loadFile(TPMStructuresXMLFile)
        val structureSeq = structures \ "structure"
        val structureNames = structureSeq.map(s => (s \ "name").text).toSet

        // create tpmCommands: List[TpmCommand]

        val commands = xml.XML.loadFile(TPMCommandsXMLFile)
        val commandSeq = commands \ "command"
        val tpmCommands_1: List[TpmCommand] = (commands \ "command").map(TpmCommand.fromXML(_)).toList
        // Do not include TPM_Init in these checks because it has no parameters
        val tpmCommands = tpmCommands_1.filter(c => c.name != "TPM_Init")

        def checkCommand(c: TpmCommand) = {

            // ==========================================================
            // checkInParams, checkOutParams
            // ==========================================================

            def checkInParams(c: TpmCommand) = {

                val ps = c.inParams.map(p => (p.name, p.typeName)).toArray
                val tagDesc = c.inParams.head.description
                val authTypes = Array("TPM_AUTHHANDLE", "TPM_NONCE", "TPM_NONCE", "BOOL", "TPM_AUTHDATA")

                def checkAuth(begin: Int, end: Int) = {
                    assert(end - begin == 5)
                    val five = ps.slice(begin, end)
                    val (names, types) = five.unzip
                    if (types.toList != authTypes.toList) println(c.name + IN_AUTH_BLOCK_ERR + types.toList)
                }

                tagDesc match {
                    case "TPM_TAG_RQU_COMMAND" => {
                        if (ps.length < 3) println(c.name + IN_TOO_FEW_AUTH0_ERR + ps.length)
                    }
                    case "TPM_TAG_RQU_AUTH1_COMMAND" => {
                        if (ps.length < 8) println(c.name + IN_TOO_FEW_AUTH1_ERR + ps.length)
                        checkAuth(ps.length - 5, ps.length)
                    }
                    case "TPM_TAG_RQU_AUTH2_COMMAND" => {
                        if (ps.length < 13) println(c.name + IN_TOO_FEW_AUTH2_ERR + ps.length)
                        checkAuth(ps.length - 5, ps.length)
                        checkAuth(ps.length - 10, ps.length - 5)
                    }
                    case _ => println(c.name + IN_TAG_DESC_ERR + tagDesc)
                }

                if (ps(0)._1 != "tag") println(c.name + IN_TAG_NAME_ERR + ps(0)._1)
                if (ps(0)._2 != "TPM_TAG") println(c.name + IN_TAG_TYPE_ERR + ps(0)._2)
                if (ps(1)._1 != "paramSize") println(c.name + IN_SIZE_NAME_ERR + ps(1)._1)
                if (ps(1)._2 != "UINT32") println(c.name + IN_SIZE_TYPE_ERR + ps(1)._2)
                if (ps(2)._1 != "ordinal") println(c.name + IN_CODE_NAME_ERR + ps(2)._1)
                if (ps(2)._2 != "TPM_COMMAND_CODE") println(c.name + IN_CODE_TYPE_ERR + ps(2)._2)
            }

            def checkOutParams(c: TpmCommand) = {

                val ps = c.outParams.map(p => (p.name, p.typeName)).toArray
                val tagDesc = c.outParams.head.description
                val authTypes = Array("TPM_NONCE", "TPM_NONCE", "BOOL", "TPM_AUTHDATA")

                def checkAuth(begin: Int, end: Int) = {
                    assert(end - begin == 4)
                    val four = ps.slice(begin, end)
                    val (names, types) = four.unzip
                    if (types.toList != authTypes.toList) println(c.name + OUT_AUTH_BLOCK_ERR + types.toList)
                }

                tagDesc match {
                    case "TPM_TAG_RSP_COMMAND" => {
                        if (ps.length < 4) println(c.name + OUT_TOO_FEW_AUTH0_ERR + ps.length)
                    }
                    case "TPM_TAG_RSP_AUTH1_COMMAND" => {
                        if (ps.length < 8) println(c.name + OUT_TOO_FEW_AUTH1_ERR + ps.length)
                        checkAuth(ps.length - 4, ps.length)
                    }
                    case "TPM_TAG_RSP_AUTH2_COMMAND" => {
                        if (ps.length < 12) println(c.name + OUT_TOO_FEW_AUTH2_ERR + ps.length)
                        checkAuth(ps.length - 4, ps.length)
                        checkAuth(ps.length - 8, ps.length - 4)
                    }
                    case _ => println(c.name + OUT_TAG_DESC_ERR + tagDesc)
                }

                if (ps(0)._1 != "tag") println(c.name + OUT_TAG_NAME_ERR + ps(0)._1)
                if (ps(0)._2 != "TPM_TAG") println(c.name + OUT_TAG_TYPE_ERR + ps(0)._2)
                if (ps(1)._1 != "paramSize") println(c.name + OUT_SIZE_NAME_ERR + ps(1)._1)
                if (ps(1)._2 != "UINT32") println(c.name + OUT_SIZE_TYPE_ERR + ps(1)._2)
                if (ps(2)._1 != "returnCode") println(c.name + OUT_RET_NAME_ERR + ps(2)._1)
                if (ps(2)._2 != "TPM_RESULT") println(c.name + OUT_RET_TYPE_ERR + ps(2)._2)                
                if (ps(3)._1 != "ordinal") println(c.name + OUT_CODE_NAME_ERR + ps(3)._1)
                if (ps(3)._2 != "TPM_COMMAND_CODE") println(c.name + OUT_CODE_TYPE_ERR + ps(3)._2)
            }

            checkInParams(c)
            checkOutParams(c)
        }

        tpmCommands.foreach(c => checkCommand(c))
    }
}