//------------------------------------------------------------------------------
//! @file CombLoops.cpp
//! @brief Algorithm for finding combinatorial loops
//
// SPDX-FileCopyrightText: Udi Finkelstein
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

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

#include "CombLoops.h"

#include "NetlistPath.h"

#include "slang/ast/SemanticFacts.h"

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

SCCResult StrongConnectedComponents::sccr_dummy;

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
SCCResult& StrongConnectedComponents::getAdjacencyList(int node) {
    auto adjListOriginal_s = adjListOriginal.size();
    lowlink.resize(adjListOriginal_s);
    number.resize(adjListOriginal_s);
    visited.resize(adjListOriginal_s);

    while (true) {
        std::fill(visited.begin(), visited.end(), false);
        stack.clear();
        currentSCCs.clear();

        makeAdjListSubgraph(node);
        for (int i = node; i < adjListOriginal_s; i++) {
            if (!visited[i]) {
                getStrongConnectedComponents(i);
                const std::vector<int>* nodes = getLowestIdComponent();
                if (nodes != nullptr && !nodes->empty() && !find_vec(*nodes, node) &&
                    !find_vec(*nodes, node + 1)) {
                    node++;
                    continue;
                }
                else if (nodes != nullptr) {
                    buildAdjList(*nodes, sccr_current);
                    auto& adjacencyList = sccr_current.getAdjListForWrite();
                    if (!adjacencyList.empty()) {
                        for (int j = 0; j < adjListOriginal_s; j++) {
                            if (!adjacencyList[j].empty()) {
                                sccr_current.setLowestNodeId(j);
                                return sccr_current;
                            }
                        }
                    }
                }
            }
        }
        return sccr_dummy;
    }
}

/**
 * Builds the adjacency-list for a subgraph containing just nodes
 * >= a given index.
 *
 * @param node Node with lowest index in the subgraph
 */
void StrongConnectedComponents::makeAdjListSubgraph(const int node) {
    adjList.clear();
    const int adjListSize = adjListOriginal.size();
    adjList.resize(adjListSize);

    for (int i = node; i < adjListSize; i++) {
        const int adjListOriginalISize = adjListOriginal[i].size();
        for (int j = 0; j < adjListOriginalISize; j++) {
            const int currentNode = adjListOriginal[i][j];
            if (currentNode >= node) {
                adjList[i].push_back(currentNode);
            }
        }
    }
}

/**
 * Calculates the strong connected component out of a set of scc's, that
 * contains the node with the lowest index.
 *
 * @return Vector::Integer of the scc containing the lowest nodenumber
 */
const std::vector<int>* StrongConnectedComponents::getLowestIdComponent() const {
    int min = adjList.size();
    const std::vector<int>* currScc = nullptr;

    for (int i = 0; i < currentSCCs.size(); i++) {
        for (int j = 0; j < currentSCCs[i].size(); j++) {
            const int node = currentSCCs[i][j];
            if (node < min) {
                currScc = &currentSCCs[i];
                min = node;
            }
        }
    }

    return currScc;
}

/**
 * Fills SCCResult with adjacency list representing the adjacency-structure
 * of the strong connected component with least vertex in the currently
 * viewed subgraph
 */
void StrongConnectedComponents::buildAdjList(const std::vector<int>& nodes, SCCResult& sccr) const {
    std::vector<std::vector<int>>& lowestIdAdjacencyList = sccr.getAdjListForWrite();
    auto nodes_s = nodes.size();
    lowestIdAdjacencyList.clear();
    lowestIdAdjacencyList.resize(adjList.size());
    if (!nodes.empty()) {
        for (int i = 0; i < nodes_s; i++) {
            int node = nodes[i];
            std::vector<int>& sccr_adjlist_node = lowestIdAdjacencyList[node];
            auto& adjList_node = adjList[node];
            sccr_adjlist_node.clear();
            const int ns = adjList_node.size();
            for (int j = 0; j < ns; j++) {
                int succ = adjList_node[j];
                if (find_vec(nodes, succ)) {
                    sccr_adjlist_node.push_back(succ);
                }
            }
        }
    }
}

/**
 * Searchs for strong connected components reachable from a given node.
 *
 * @param root node to start from.
 */
void StrongConnectedComponents::getStrongConnectedComponents(int root) {
    sccCounter++;
    lowlink[root] = sccCounter;
    number[root] = sccCounter;
    visited[root] = true;
    stack.push_back(root);

    for (int i = 0; i < adjList[root].size(); i++) {
        int w = adjList[root][i];
        if (!visited[w]) {
            getStrongConnectedComponents(w);
            lowlink[root] = std::min(lowlink[root], lowlink[w]);
        }
        else if (number[w] < number[root]) {
            if (find_vec(stack, w)) {
                lowlink[root] = std::min(lowlink[root], number[w]);
            }
        }
    }

    if ((lowlink[root] == number[root]) && !stack.empty()) {
        int next;
        std::vector<int> scc;

        do {
            next = stack.back();
            stack.pop_back();
            scc.push_back(next);
        } while (number[next] > number[root]);

        if (scc.size() > 1) {
            currentSCCs.push_back(scc);
        }
    }
}

/**
 * Constructor.
 *
 * Go over the node list in the Netlist object, skipping any nodes
 * driven on edge (pos or neg), and any edges terminating on such nodes.
 *
 * @param matrix adjacency-matrix of the graph
 * @param netlist pointer to the full netlist
 */
ElementaryCyclesSearch::ElementaryCyclesSearch(Netlist& netlist) {
    int nodes_num = netlist.numNodes();
    auto node_0 = netlist.getNode(0).ID;
    adjList.resize(nodes_num);
    auto net_nodes = nodes_num;
    DEBUG_PRINT("Nodes: {}\n", nodes_num);
    for (size_t i = 0; i < nodes_num; i++) {
        auto& node = netlist.getNode(i);
        if (node.edgeKind != slang::ast::EdgeKind::None) {
            DEBUG_PRINT("skipped node {}\n", node.ID);
            net_nodes--;
            continue;
        }
        int node_edges_num = node.getEdges().size();
        adjList[i].clear();
        for (int j = 0; j < node_edges_num; j++) {
            auto& edge = *(node.getEdges()[j]);
            if (edge.disabled)
                continue;
            auto& tnode = edge.getTargetNode();
            if (tnode.edgeKind != slang::ast::EdgeKind::None) {
                DEBUG_PRINT("skipped tnode {}\n", tnode.ID);
                continue;
            }
            adjList[i].push_back(tnode.ID - node_0);
        }
    }
    DEBUG_PRINT("Actual active Nodes: {}\n", net_nodes);
}

/**
 * Returns List::List::Object with the Lists of nodes of all elementary
 * cycles in the graph.
 *
 * @return List::List::Object with the Lists of the elementary cycles.
 */
std::vector<CycleListType>* ElementaryCyclesSearch::getElementaryCycles() {
    cycles.clear();
    blocked.resize(adjList.size(), false);
    B.resize(adjList.size());
    stack.clear();
    StrongConnectedComponents sccs(adjList);
    ID_type s = 0;

    while (true) {
        const SCCResult& sccResult = sccs.getAdjacencyList(s);
        if (!sccResult.isEmpty() && !sccResult.getAdjList().empty()) {
            const std::vector<std::vector<ID_type>>& scc = sccResult.getAdjList();
            s = sccResult.getLowestNodeId();
            for (int j = 0; j < scc.size(); j++) {
                if (!scc[j].empty()) {
                    blocked[j] = false;
                    B[j].clear();
                }
            }

            findCycles(s, s, scc);
            s++;
        }
        else {
            break;
        }
    }

    return &(this->cycles);
}

#ifdef DEBUG
/**
 * These are useful when debugging but are not needed otherwise
 */
void ElementaryCyclesSearch::getHierName(NetlistNode& node, std::string& buffer) {
    switch (node.kind) {
        case NodeKind::PortDeclaration: {
            auto& portDecl = node.as<NetlistPortDeclaration>();
            buffer = "Port declaration: ";
            buffer.append(portDecl.hierarchicalPath);
            break;
        }
        case NodeKind::VariableDeclaration: {
            auto& varDecl = node.as<NetlistVariableDeclaration>();
            buffer = "Variable declaration: ";
            buffer.append(varDecl.hierarchicalPath);
            break;
        }
        case NodeKind::VariableAlias: {
            auto& varAlias = node.as<NetlistVariableAlias>();
            buffer = "Variable alias ";
            buffer.append(varAlias.hierarchicalPath);
            break;
        }
        case NodeKind::VariableReference: {
            auto& varRef = node.as<NetlistVariableReference>();
            buffer = varRef.toString();
            if (!varRef.isLeftOperand())
                break;
            if (node.edgeKind == slang::ast::EdgeKind::None)
                buffer.append(" (Assigned to)");
            else {
                buffer.append(" (Assigned to @(");
                buffer.append(toString(node.edgeKind));
                buffer.append(")");
            }
            break;
        }
        default:
            SLANG_UNREACHABLE;
    }
}

void ElementaryCyclesSearch::dumpAdjList(Netlist& netlist) {
    std::string buffer_s;
    std::string buffer_d;
    for (int i = 0; i < adjList.size(); i++) {
        auto l = adjList[i];
        auto ls = l.size();
        ElementaryCyclesSearch::getHierName(netlist.getNode(i), buffer_s);
        for (int j = 0; j < ls; j++) {
            ElementaryCyclesSearch::getHierName(netlist.getNode(l[j]), buffer_d);
            std::cout << buffer_s << " => " << buffer_d << std::endl;
        }
    }
}
#endif

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
bool ElementaryCyclesSearch::findCycles(ID_type v, ID_type s,
                                        const std::vector<std::vector<ID_type>>& adjList) {
    bool f = false;
    stack.push_back(v);
    blocked[v] = true;

    for (int i = 0; i < adjList[v].size(); i++) {
        ID_type w = adjList[v][i];

        if (w == s) {
            CycleListType cycle;
            for (int j = 0; j < stack.size(); j++) {
                ID_type index = stack[j];
                cycle.push_back(index);
            }
            cycles.push_back(cycle);
            f = true;
        }
        else if (!this->blocked[w]) {
            if (this->findCycles(w, s, adjList)) {
                f = true;
            }
        }
    }

    if (f) {
        this->unblock(v);
    }
    else {
        for (int i = 0; i < adjList[v].size(); i++) {
            ID_type w = adjList[v][i];
            if (!find_vec(B[w], v)) {
                B[w].push_back(v);
            }
        }
    }

    stack.erase(remove(stack.begin(), stack.end(), v), stack.end());
    return f;
}

/**
 * Unblocks recursivly all blocked nodes, starting with a given node.
 *
 * @param node node to unblock
 */
void ElementaryCyclesSearch::unblock(ID_type node) {
    this->blocked[node] = false;
    std::vector<ID_type> Bnode = this->B[node];
    while (!Bnode.empty()) {
        ID_type w = Bnode.front();
        Bnode.erase(Bnode.begin());
        if (this->blocked[w]) {
            this->unblock(w);
        }
    }
}
