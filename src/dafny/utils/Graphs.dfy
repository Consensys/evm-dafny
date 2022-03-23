/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */
 
include "../refinement/evm-seq.dfy"
/**
 *  Provide labelled directed graph.
 */
 module Graphs {

    import opened EVMSeq 

    /** A labelled directed edge: (label, successor). */
    type LabDiEdge<!S> = (EVMInst<S>, nat)

    /** A labelled directed graph as a map src -> [(l1, tgt1), (l2, tgt2), ...] */  
    type LabDiGraph<!S> = map<nat, seq<LabDiEdge<S>>>

    /**
     *  Print an edge in DOT format.
     *  @param  e   A directed edge.
     */
    method {:verify true} edgeToDOT(src: nat, tgt: nat, l: string)  
    {
        print src, " -> ", tgt, " [label=\"", l, "\"]", ";\n";
    }

    /**
     *  Print a DiGraph in DOT format.
     *  @param  g           A directed graph.
     *  @param  n           Number of nodes in the graph. Assumption is that node 0 is initial location and node n - 1 is final location.
     *  @param  name        Optional label of the graph.
     *  @param  tooltip     Optional map providing tooltips for nodes.
     *  @returns            Whether there exists a (source) node in `g` that did not have any associated set of edges.
     */
    method {:verify true} diGraphToDOT<S>(g: LabDiGraph<S>, n: nat, name: string := "noName", tooltip: map<nat, string> := map[]) returns (ghost r: bool) 
        /** If the set of nodes in the graph is exactly [0..n[ then "not found" is never printed out. */
        ensures (forall k:: k in g <==> 0 <= k < n) ==> r 
    {
        r := true;
        print "digraph G {\n";
        print "\tfontname=helvetica;\n";
        print "\tgraph [pad=\"1.5\", ranksep=\"1.2\", nodesep=\"0.4\"];\n";
        print "\tfontsize=\"10.0\"\n";
        print "\tlabel=\"", name, "\";\n";
        print "\trankdir=\"TB\"\n";
        print "\tnode [shape=circle,style=filled,fillcolor=black,fontcolor=white]\n";
        print "// Graph\n";

        //  Initial and final locations.
        print "0 [fillcolor=green, style=filled];\n";
        if n > 0 {
            print n - 1, " [fillcolor=red, style=filled];\n";
        }
        for i := 0 to n {
                if i in tooltip {
                    print i, " [tooltip=\"",tooltip[i],"\"];\n";
                }
            }
        //  Edges.
        for i := 0 to n 
             invariant (forall k :: k in g <==> 0 <= k < n) ==> r 
        {
            if i in g {
                //  print all the successors
                for k := 0 to |g[i]| {
                        edgeToDOT(i, g[i][k].1, g[i][k].0.name);
                } 
            } else {
                r := false;
                print "Element", i, " not found in map";
            }
        }
        print "}\n";
    }
 }
