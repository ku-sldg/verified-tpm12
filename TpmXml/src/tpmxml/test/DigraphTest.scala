package tpmxml.test

import tpmxml.util.Digraph
import scala.collection.immutable.{SortedSet, SortedMap}

object DigraphTest {

    def main(args: Array[String]) {
    	
        val edgeSet = Set(("u", "v"), ("u", "x"), ("v", "y"), ("w", "y"), ("w", "z"),
                ("x", "v"), ("y", "x"), ("z", "z"))
                
        val myGraph = Digraph(Set("a"), edgeSet)
        
        /*
         * GWK: Would be nice to print all these out so that they are sorted.
         */
        
        println("Graph = " + myGraph.toString)
        println("Vertices = " + SortedSet((myGraph.vertexSet.toSeq): _*).toString)
        println("Edges = " + SortedSet((myGraph.edgeSet.toSeq): _*).toString)
        println("Out degree = " + myGraph.outDegree)
        println("In degree = " + myGraph.inDegree)
    }
    
}