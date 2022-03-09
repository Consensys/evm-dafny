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

    // datatype DiEdge<!S> = DiEdge(src: S, dst: S)  

    datatype LabDiEdge<!S> = LabDiEdge(src: S, dst: S, name: string)  

    /** A Directed graph. Type of edges must support equality. */
    // type DiGraph<!S(==)> = seq<DiEdge>

    type LabDiGraph<!S(==)> = seq<LabDiEdge>

    function method union(d1: LabDiGraph, d2: LabDiGraph): LabDiGraph
    {
        d1 + d2
    }

    /**
     *  Print an edge in DOT format.
     *  @param  e   A directed edge.
     *  @param  f   A converter from `S` to a printable string.
     */
    method edgeToDOT<S>(e: LabDiEdge) 
    {
        print e.src, " -> ", e.dst, "[label=\"", e.name, "\"]", ";\n";
    }

    /**
     *  Print a DiGraph in DOT format.
     *  @param  g   A directed graph.
     *  @param  f   A converter from `S` to a printable string.
     */
    method diGraphToDOT(g: LabDiGraph<int>) 
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
