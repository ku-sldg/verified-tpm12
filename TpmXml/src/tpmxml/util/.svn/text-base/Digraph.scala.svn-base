package tpmxml.util

import scala.collection.mutable
import scala.collection.immutable.{SortedSet, SortedMap}

class Digraph[A](verts: Set[A], val edges: Set[(A, A)]) {

    val edgeSet = edges
    val (edgeDomain, edgeRange) = edgeSet.unzip
    val vertexSet = edgeDomain | edgeRange | verts
    val isolated = vertexSet &~ (edgeDomain | edgeRange)

    def adjList(): Map[A, Set[A]] = {
        val emptyMultiMap = new mutable.HashMap[A, mutable.Set[A]] with mutable.MultiMap[A, A]
        val emptySet: mutable.Set[A] = mutable.Set.empty
        val mmap = edgeSet.foldLeft (emptyMultiMap) { (m, e) => m.addBinding(e._1, e._2) }
        isolated.foreach(v => mmap += (v -> emptySet))
        mmap.mapValues(_.toSet).toMap
    }

    def outDegree: Map[A, Int] = adjList.toList.map(kv => (kv._1, kv._2.size)).toMap

    def transpose = {
        def flipEdge(edge: (A, A)) = (edge._2, edge._1)

        val flippedEdgeSet = edgeSet.map(e => flipEdge(e))
        Digraph(isolated, flippedEdgeSet)
    }

    def inDegree: Map[A, Int] = transpose.outDegree
    
    /*
     * TODO For all remove methods, what if you remove something that does not exist?
     */
    
    def remove(v: A): Digraph[A] = {
        val newVerts = isolated - v
        val newEdges = edgeSet.filter(e => v != e._1 && v != e._2)
        Digraph(newVerts, newEdges)
    }
    
    def remove(e: (A, A)): Digraph[A] = {
        val newVerts = isolated + e._1 + e._2
        val newEdges = edgeSet - e
        Digraph(newVerts, newEdges)
    }
    
    def remove(vs: Set[A]): Digraph[A] = {
        val newVerts = isolated &~ vs
        val newEdges = edgeSet.filter(e => !vs.contains(e._1) && !vs.contains(e._2))
        Digraph(newVerts, newEdges)
    }
    
    def zeroOutDegreeVerts(): Set[A] = edgeSet.foldLeft (vertexSet) { (s, e) => s - e._1 }
    
    def stratifiedTopoSort(): Seq[Set[A]] = {
        
        var result: List[Set[A]] = List.empty
        var currDigraph: Digraph[A] = this
        var zeros: Set[A] = zeroOutDegreeVerts
        
        while (zeros.nonEmpty) {
            result = zeros :: result
            currDigraph = currDigraph.remove(zeros)
            zeros = currDigraph.zeroOutDegreeVerts
        }
        
        result
    }
    
    override def toString() = adjList.toString()
}

object Digraph {

    def apply[A](vertexSet: Set[A], edgeSet: Set[(A, A)]) = new Digraph(vertexSet, edgeSet)
}