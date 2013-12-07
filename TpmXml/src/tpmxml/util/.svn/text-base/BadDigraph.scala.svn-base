package tpmxml.util

import scala.collection.mutable

class BadDigraph[A](adjList: mutable.MultiMap[A, A]) {

    /*
     * Used keys.toSet instead of keySet just so they would be immutable Set like edges
     */
    def vertices = adjList.keys.toSet
    
    def edges = adjList.map(p => p._2.map(t => (p._1, t))).flatten.toSet
    
    def outDegree: Map[A, Int] = adjList.toList.map(kv => (kv._1, kv._2.size)).toMap
    
    def transpose = {
        def flipEdge(edge: (A, A)) = (edge._2, edge._1)
        
        val flippedEdges = this.edges.map(e => flipEdge(e))
        BadDigraph(flippedEdges)
    }

    def inDegree: Map[A, Int] = this.transpose.outDegree
    
    override def toString() = adjList.toString()
}

object BadDigraph {
    
//    def apply[A](edges: (A, A)*): Digraph[A] = {
//        
//    	def pairs2multimap[A, B](pairs: (A, B)*) = {
//    		val emptyMultiMap = new mutable.HashMap[A, mutable.Set[B]] with mutable.MultiMap[A, B]
//    		pairs.foldLeft(emptyMultiMap) { (acc, pair) => acc.addBinding(pair._1, pair._2) }
//    	}
//
//    	/*
//    	 * GWK: Note the requirement to add _* for the type
//    	 */
//        new Digraph[A](pairs2multimap(edges: _*))
//    }

    def apply[A](adjList: mutable.MultiMap[A, A]) = new BadDigraph(adjList)

    def apply[A](edgeSet: Set[(A, A)]): BadDigraph[A] = {
        
    	def pairs2multimap[A, B](pairs: Set[(A, B)]) = {
    		val emptyMultiMap = new mutable.HashMap[A, mutable.Set[B]] with mutable.MultiMap[A, B]
    		pairs.foldLeft(emptyMultiMap) { (acc, pair) => acc.addBinding(pair._1, pair._2) }
    	}

        new BadDigraph[A](pairs2multimap(edgeSet))
    }
}