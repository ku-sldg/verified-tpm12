package tpmxml.util

object CaseConverter {

    val camelSplitter = """(?<!(^|[A-Z]))(?=[A-Z])|(?<!^)(?=[A-Z][a-z])""" 
    
    /*
     * Converts camel case text to dash-separated lower case.
     * 
     * Examples: myName ==> my-name; myXMLUniqueID ==> my-xml-unique-id
     */
    def camelToDash(s: String): String = {
        s.split(camelSplitter).mkString("-").toLowerCase
    }

    /*
     * Converts camel case text to underscore-separated upper case.
     * 
     * Examples: myName ==> MY_NAME; myXMLUniqueID ==> MY_XML_UNIQUE_ID
     */
    def camelToSnake(s: String): String = {
        s.split(camelSplitter).mkString("_").toUpperCase
    }
    
    /*
     * Converts dash-separated text to camel case.
     * 
     * Examples: my-name ==> myName; My-XML-unique-ID ==> myXmlUniqueID
     */
    def dashToCamel(s: String): String = {
        val capCamel = s.split("""-+""").map(s => s.head.toUpper + s.tail.toLowerCase).mkString("")
        uncapitalize(capCamel)
    }
    
    /*
     * Converts dash-separated text to underscore-separated upper case .
     * 
     * Examples: my-name ==> MY_NAME; My-XML-unique-ID ==> MY_XML_UNIQUE_ID
     */
    def dashToSnake(s: String): String = {
        s.split("""-+""").mkString("_").toUpperCase
    }
    
    /*
     * Converts underscore-separated text to camel case.
     * 
     * Examples: MY_NAME ==> myName; My_XML_unique_ID ==> myXmlUniqueId
     */
    def snakeToCamel(s: String): String = {
        val capCamel = s.split("""_+""").map(s => s.head.toUpper + s.tail.toLowerCase).mkString("")
        uncapitalize(capCamel)
    }

    /*
     * Converts underscore-separated text to dash-separated lower case.
     * 
     * Examples: MY_NAME ==> my-name; My_XML_unique_ID ==> my-xml-unique-id
     */
    def snakeToDash(s: String): String = {
        s.split("""_+""").mkString("-").toLowerCase
    }

    def capitalize(s: String) = {
        s.head.toUpper + s.tail
    }
    
    def uncapitalize(s: String) = {
        s.head.toLower + s.tail
    }
}