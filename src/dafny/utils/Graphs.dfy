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
 
/**
 *  Provide labelled directed graph.
 */
 module Graphs {

    /** A labelled directed edge: (src, dst, label). */
    type LabDiEdge<!S> = (S, S, string)

    /** A Directed graph. Type of edge is not a reference. */
    type LabDiGraph<!S> = seq<LabDiEdge>

    /**
     *  Print an edge in DOT format.
     *  @param  e   A directed edge.
     */
    method {:verify false} edgeToDOT<S>(e: LabDiEdge) 
    {
        print e.0, " -> ", e.1, " [label=\"", e.2, "\"]", ";\n";
    }

    /**
     *  Print a DiGraph in DOT format.
     *  @param  g           A directed graph.
     *  @param  n           Number of nodes in the graph. Assumption is that node 0 is initial location and node n - 1 is final location.
     *  @param  name        Optional label of the graph.
     *  @param  tooltip     Optional map providing tooltips for nodes.
     */
    method {:verify true} diGraphToDOT(g: LabDiGraph<nat>, n: nat, name: string := "noName", tooltip: map<nat, string> := map[]) 
    {
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
            print n - 1, " [fillcolor=blue, style=filled];\n";

        for i := 0 to n 
            {
                if i in tooltip {
                    print i, " [tooltip=\"",tooltip[i],"\"];\n";
                }
            }
        }
        //  Edges.
        for i := 0 to |g|
        {
            edgeToDOT(g[i]);
        }
        print "}\n";
    }

 }
