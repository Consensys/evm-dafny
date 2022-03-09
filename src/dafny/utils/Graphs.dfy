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
 

 module Graphs {

    type LabDiEdge<!S> = (S, S, string)

    /** A Directed graph. Type of edges must support equality. */
    type LabDiGraph<!S(==)> = seq<LabDiEdge>


    /**
     *  Print an edge in DOT format.
     *  @param  e   A directed edge.
     *  @param  f   A converter from `S` to a printable string.
     */
    method edgeToDOT<S>(e: LabDiEdge) 
    {
        print e.0, " -> ", e.1, "[label=\"", e.2, "\"]", ";\n";
    }

    /**
     *  Print a DiGraph in DOT format.
     *  @param  g   A directed graph.
     *  @param  f   A converter from `S` to a printable string.
     */
    method diGraphToDOT(g: LabDiGraph<nat>) 
        // requires |g| >= 1
    {
        print "digraph G {\n";
        print "\tfontname=helvetica;\n";
        print "\tgraph [pad=\"0.5\", ranksep=\"1.0\", nodesep=\"0.1\"];";
        print "\tfontsize=\"56.0\"\n";
        // print label="arb-bridge-eth/contracts"
        print "\trankdir=\"DT\"\n";
        print "// Graph\n";
        for i := 0 to |g|
        {
            edgeToDOT(g[i]);
        }
        print "}\n";
    }

 }
