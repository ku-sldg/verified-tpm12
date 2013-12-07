package tpmxml.util

import tpmxml.data.TpmStructure

object DependencySorter {

    def sortStructures(ss: List[TpmStructure]): Array[List[TpmStructure]] = {

        def getDepSet(s: TpmStructure): Set[(String, String)] = {
            def isPrimitive(s: String) = s.startsWith("BOOL") || s.startsWith("UINT") || s.startsWith("BYTE")
            def arrAdjust(s: String): String = if (s.endsWith("[]")) s.dropRight(2) else s
            
            if (s.fields.nonEmpty) {
                s.fields.filter { f => !isPrimitive(f.typeName) } map { f => (s.name, arrAdjust(f.typeName)) } toSet
            } else {
                if (s.values.isEmpty && !isPrimitive(s.typedef))
                    Set((s.name, arrAdjust(s.typedef)))
                else
                    Set.empty
            }
        }

        val sMap: Map[String, TpmStructure] = ss.map(s => (s.name, s)).toMap

        val ChapterSection = """(\d+)\.(\d+)""".r
        
        def chapter(s: String): Int = s match {
            case ChapterSection(ch, sc) => ch.toInt
            case _ => { println("misformatted section: " + s); 0 }
        }
        
        def majorSection(s: String): Int = s match {
            case ChapterSection(ch, sc) => sc.toInt
            case _ => 0            
        }

        def sortBySecName(xs: List[String]): List[TpmStructure] = {
            val structs = xs.map(str => sMap(str))
            structs.sortBy(s => (chapter(s.section), majorSection(s.section), s.name))
        }

        def warning(name: String, undef: String) = "Warning: " + name + " depends on undefined type: " + undef

        val nodes: Set[String] = ss.map(_.name).toSet
        val deps: Set[(String, String)] = ss.map(s => getDepSet(s)).flatten.toSet
        deps.foreach { dep => if (!nodes.contains(dep._2)) println(warning(dep._1, dep._2)) }
        val depGraph = Digraph(nodes, deps)
        val strata: Seq[Set[String]] = depGraph.stratifiedTopoSort
        val sortedStrata: Seq[List[TpmStructure]] = strata.map(ns => sortBySecName(ns.toList))
        return sortedStrata.reverse.toArray
    }
}