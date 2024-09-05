//------------------------------------------------------------------------------
//! @file CombLoops.h
//! @brief Algorithm for finding combinatorial loops
//
// SPDX-FileCopyrightText: Udi Finkelstein
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#ifndef COMBLOOPS_H
#define COMBLOOPS_H

/*
 * This code is derived from C++ code created by me (Udi finkelstein),
 * which is a translation of the Java code at https://github.com/josch/cycles_johnson_meyer
 * Due to this reason, I include the original author's license file.
 */

/*
 * (BSD-2 license)
 *
 * Copyright (c) 2012, Frank Meyer
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * Redistributions of source code must retain the above copyright notice, this list of conditions
 * and the following disclaimer. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the documentation and/or other
 * materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 * FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
 * WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#include "Netlist.h"
#include <algorithm>
#include <any>
#include <vector>

using namespace netlist;
using ID_type = int;

template<typename T>
bool find_vec(const std::vector<T>& vec, const T& val) {
    return std::find(vec.cbegin(), vec.cend(), val) != vec.end();
}

template<typename T, typename Predicate>
bool find_vec_if(const std::vector<T>& vec, Predicate predicate) {
    return std::find_if(vec.cbegin(), vec.cend(), predicate) != vec.end();
}
template<typename T, typename Predicate>
int count_vec_if(const std::vector<T>& vec, Predicate predicate) {
    return std::count_if(vec.cbegin(), vec.cend(), predicate);
}

class SCCResult {
private:
    std::vector<std::vector<ID_type>> adjList;
    ID_type lowestNodeId;

public:
    SCCResult(std::vector<std::vector<ID_type>>& adjList, ID_type lowestNodeId) :
        adjList(adjList), lowestNodeId(lowestNodeId) {}
    SCCResult(std::vector<std::vector<ID_type>>& adjList) : adjList(adjList), lowestNodeId(-1) {}
    SCCResult() : lowestNodeId(-1) {}
    inline std::vector<std::vector<ID_type>>& getAdjListForWrite() { return adjList; }
    inline const std::vector<std::vector<ID_type>>& getAdjList() const { return adjList; }
    inline const ID_type getLowestNodeId() const { return lowestNodeId; }
    inline void setLowestNodeId(ID_type node_id) { lowestNodeId = node_id; }
    inline bool isEmpty() const { return lowestNodeId == -1; }
};

/**
 * This is a helpclass for the search of all elementary cycles in a graph
 * with the algorithm of Johnson. For this it searches for strong connected
 * components, using the algorithm of Tarjan. The constructor gets an
 * adjacency-list of a graph. Based on this graph, it gets a nodenumber s,
 * for which it calculates the subgraph, containing all nodes
 * {s, s + 1, ..., n}, where n is the highest nodenumber in the original
 * graph (e.g. it builds a subgraph with all nodes with higher or same
 * nodenumbers like the given node s). It returns the strong connected
 * component of this subgraph which contains the lowest nodenumber of all
 * nodes in the subgraph.<br><br>
 *
 * For a description of the algorithm for calculating the strong connected
 * components see:<br>
 * Robert Tarjan: Depth-first search and linear graph algorithms. In: SIAM
 * Journal on Computing. Volume 1, Nr. 2 (1972), pp. 146-160.<br>
 * For a description of the algorithm for searching all elementary cycles in
 * a directed graph see:<br>
 * Donald B. Johnson: Finding All the Elementary Circuits of a Directed Graph.
 * SIAM Journal on Computing. Volumne 4, Nr. 1 (1975), pp. 77-84.<br><br>
 *
 * @author Frank Meyer, web_at_normalisiert_dot_de
 * @version 1.1, 22.03.2009
 *
 */

class StrongConnectedComponents {
private:
    /** Adjacency-list of original graph */
    std::vector<std::vector<ID_type>>& adjListOriginal;

    /** Adjacency-list of currently viewed subgraph */
    /* node IDs are the same as the original, but some of the nodes will be filtered, below a
     * specific node ID*/
    std::vector<std::vector<ID_type>> adjList;

    /** Helpattribute for finding scc's */
    std::vector<bool> visited;

    /** Helpattribute for finding scc's */
    std::vector<int> stack;

    /** Helpattribute for finding scc's */
    std::vector<int> lowlink;

    /** Helpattribute for finding scc's */
    std::vector<int> number;

    /** Helpattribute for finding scc's */
    int sccCounter = 0;

    /** Helpattribute for finding scc's */
    std::vector<std::vector<ID_type>> currentSCCs;

    // we only need one object at a time
    SCCResult sccr_current;

public:
    static SCCResult sccr_dummy;
    /**
     * Constructor.
     *
     * @param adjList adjacency-list of the graph
     */
    StrongConnectedComponents(std::vector<std::vector<ID_type>>& adjList) :
        adjListOriginal(adjList) {};

    /**
     * This method returns the adjacency-structure of the strong connected
     * component with the least vertex in a subgraph of the original graph
     * induced by the nodes {s, s + 1, ..., n}, where s is a given node. Note
     * that trivial strong connected components with just one node will not
     * be returned.
     *
     * @param node node s
     * @return SCCResult with adjacency-structure of the strong
     * connected component; null, if no such component exists
     */
    SCCResult& getAdjacencyList(ID_type node);

private:
    void makeAdjListSubgraph(const ID_type node);
    const std::vector<ID_type>* getLowestIdComponent() const;
    void buildAdjList(const std::vector<ID_type>& nodes, SCCResult& sccr) const;
    void getStrongConnectedComponents(ID_type root);
};

/**
 * Searchs all elementary cycles in a given directed graph. The implementation
 * is independent from the concrete objects that represent the graphnodes, it
 * just needs an array of the objects representing the nodes the graph
 * and an adjacency-matrix of type boolean, representing the edges of the
 * graph. It then calculates based on the adjacency-matrix the elementary
 * cycles and returns a list, which contains lists itself with the objects of the
 * concrete graphnodes-implementation. Each of these lists represents an
 * elementary cycle.<br><br>
 *
 * The implementation uses the algorithm of Donald B. Johnson for the search of
 * the elementary cycles. For a description of the algorithm see:<br>
 * Donald B. Johnson: Finding All the Elementary Circuits of a Directed Graph.
 * SIAM Journal on Computing. Volumne 4, Nr. 1 (1975), pp. 77-84.<br><br>
 *
 * The algorithm of Johnson is based on the search for strong connected
 * components in a graph. For a description of this part see:<br>
 * Robert Tarjan: Depth-first search and linear graph algorithms. In: SIAM
 * Journal on Computing. Volume 1, Nr. 2 (1972), pp. 146-160.<br>
 *
 * @author Frank Meyer, web_at_normalisiert_dot_de
 * @version 1.2, 22.03.2009
 *
 */
using CycleListType = std::vector<ID_type>;

class ElementaryCyclesSearch {
private:
    /** List of cycles */
    std::vector<CycleListType> cycles;

    /** Adjacency-list of graph */
    std::vector<std::vector<ID_type>> adjList;

    /** Blocked nodes, used by the algorithm of Johnson */
    std::vector<bool> blocked;

    /** B-Lists, used by the algorithm of Johnson */
    std::vector<std::vector<ID_type>> B;

    /** Stack for nodes, used by the algorithm of Johnson */
    std::vector<ID_type> stack;

public:
    /**
     * Constructor.
     *
     * @param matrix adjacency-matrix of the graph
     * @param netlist pointer to the full netlist
     */
    ElementaryCyclesSearch(Netlist& netlist);
    /**
     * Returns List::List::Object with the Lists of nodes of all elementary
     * cycles in the graph.
     *
     * @return List::List::Object with the Lists of the elementary cycles.
     */
    std::vector<CycleListType>* getElementaryCycles();
    /**
     * Dumps the cycles found
     */
    static void getHierName(NetlistNode& node, std::string& buffer);
    void dumpAdjList(Netlist& netlist);

private:
    /**
     * Calculates the cycles containing a given node in a strongly connected
     * component. The method calls itself recursivly.
     *
     * @param v
     * @param s
     * @param adjList adjacency-list with the subgraph of the strongly
     * connected component s is part of.
     * @return true, if cycle found; false otherwise
     */
    bool findCycles(ID_type v, ID_type s, const std::vector<std::vector<ID_type>>& adjList);
    /**
     * Unblocks recursivly all blocked nodes, starting with a given node.
     *
     * @param node node to unblock
     */
    void unblock(ID_type node);
};

#endif // COMBLOOPS_H
