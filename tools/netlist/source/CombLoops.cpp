#include <vector>
#include <algorithm>
#include "slang/ast/SemanticFacts.h"
#include "CombLoops.h"

using namespace std;

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
std::vector<std::vector<int>> dummyAadjList = {};
SCCResult StrongConnectedComponents::dummy(dummyAadjList, -1);

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
SCCResult StrongConnectedComponents::getAdjacencyList(int node) {
    this->visited.resize(this->adjListOriginal.size(), false);
    std::fill(this->visited.begin(), this->visited.end(), false);
    this->lowlink.resize(this->adjListOriginal.size());
    this->number.resize(this->adjListOriginal.size());
    this->stack.clear();
    this->currentSCCs.clear();

    this->makeAdjListSubgraph(node);

    for (int i = node; i < this->adjListOriginal.size(); i++) {
        if (!this->visited[i]) {
            this->getStrongConnectedComponents(i);
            vector<int> nodes = this->getLowestIdComponent();
            if (!nodes.empty() && find(nodes.begin(), nodes.end(), node) == nodes.end() && find(nodes.begin(), nodes.end(), node + 1) == nodes.end()) {
                return this->getAdjacencyList(node + 1);
            } else {
                vector<vector<int>> adjacencyList = this->getAdjList(nodes);
                if (!adjacencyList.empty()) {
                    for (int j = 0; j < this->adjListOriginal.size(); j++) {
                        if (!adjacencyList[j].empty()) {
                            return *new SCCResult(adjacencyList, j);
                        }
                    }
                }
            }
        }
    }

    return StrongConnectedComponents::dummy;
}

/**
 * Builds the adjacency-list for a subgraph containing just nodes
 * >= a given index.
 *
 * @param node Node with lowest index in the subgraph
 */
void StrongConnectedComponents::makeAdjListSubgraph(int node) {
    this->adjList.clear();
    this->adjList.resize(this->adjListOriginal.size());

    for (int i = node; i < this->adjList.size(); i++) {
        for (int j = 0; j < this->adjListOriginal[i].size(); j++) {
            if (this->adjListOriginal[i][j] >= node) {
                this->adjList[i].push_back(this->adjListOriginal[i][j]);
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
vector<int> StrongConnectedComponents::getLowestIdComponent() {
    int min = this->adjList.size();
    vector<int> currScc;

    for (int i = 0; i < this->currentSCCs.size(); i++) {
        for (int j = 0; j < this->currentSCCs[i].size(); j++) {
            int node = this->currentSCCs[i][j];
            if (node < min) {
                currScc = this->currentSCCs[i];
                min = node;
            }
        }
    }

    return currScc;
}

/**
 * @return Vector[]::Integer representing the adjacency-structure of the
 * strong connected component with least vertex in the currently viewed
 * subgraph
 */
vector<vector<int>> StrongConnectedComponents::getAdjList(vector<int> nodes) {
    vector<vector<int>> lowestIdAdjacencyList;

    if (!nodes.empty()) {
        lowestIdAdjacencyList.resize(this->adjList.size());
        for (int i = 0; i < nodes.size(); i++) {
            int node = nodes[i];
            for (int j = 0; j < this->adjList[node].size(); j++) {
                int succ = this->adjList[node][j];
                if (find(nodes.begin(), nodes.end(), succ) != nodes.end()) {
                    lowestIdAdjacencyList[node].push_back(succ);
                }
            }
        }
    }

    return lowestIdAdjacencyList;
}

/**
 * Searchs for strong connected components reachable from a given node.
 *
 * @param root node to start from.
 */
void StrongConnectedComponents::getStrongConnectedComponents(int root) {
    this->sccCounter++;
    this->lowlink[root] = this->sccCounter;
    this->number[root] = this->sccCounter;
    this->visited[root] = true;
    this->stack.push_back(root);

    for (int i = 0; i < this->adjList[root].size(); i++) {
        int w = this->adjList[root][i];
        if (!this->visited[w]) {
            this->getStrongConnectedComponents(w);
            this->lowlink[root] = min(this->lowlink[root], this->lowlink[w]);
        } else if (this->number[w] < this->number[root]) {
            if (find(this->stack.begin(), this->stack.end(), w) != this->stack.end()) {
                this->lowlink[root] = min(this->lowlink[root], this->number[w]);
            }
        }
    }

    if ((this->lowlink[root] == this->number[root]) && !this->stack.empty()) {
        int next = -1;
        vector<int> scc;

        do {
            next = this->stack.back();
            this->stack.pop_back();
            scc.push_back(next);
        } while (this->number[next] > this->number[root]);

        if (scc.size() > 1) {
            this->currentSCCs.push_back(scc);
        }
    }
}

/**
 * Constructor.
 *
 * @param matrix adjacency-matrix of the graph
 * @param netlist pointer to the full netlist 
 */
ElementaryCyclesSearch::ElementaryCyclesSearch(std::vector<std::vector<ID_type>>& adjList) :
    adjList(adjList) { }
ElementaryCyclesSearch::ElementaryCyclesSearch(Netlist& netlist) {
    int nodes_num = netlist.numNodes();
    adjList.resize(nodes_num);
    std::cout << "Nodes: " << nodes_num << std::endl;
    for (size_t i = 0; i < nodes_num; i++) {
        auto& node = netlist.getNode(i);
        if (node.edgeKind != slang::ast::EdgeKind::None) {
            DEBUG_PRINT("skipped node {}\n", node.ID);
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
            adjList[i].push_back(tnode.ID - 1);
        }
    }
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
    StrongConnectedComponents sccs(this->adjList);
    ID_type s = 0;

    while (true) {
        SCCResult sccResult = sccs.getAdjacencyList(s);
        if ((sccResult.getLowestNodeId() != -1) && !sccResult.getAdjList().empty()) {
            std::vector<std::vector<ID_type>> scc = sccResult.getAdjList();
            s = sccResult.getLowestNodeId();
            for (int j = 0; j < scc.size(); j++) {
                if (!scc[j].empty()) {
                    blocked[j] = false;
                    B[j].clear();
                }
            }

            this->findCycles(s, s, scc);
            s++;
        } else {
            break;
        }
    }

    return &(this->cycles);
}

void ElementaryCyclesSearch::getHierName(NetlistNode& node, std::string& buffer) {
    switch (node.kind) {
        case NodeKind::PortDeclaration: {
            auto& portDecl = node.as<NetlistPortDeclaration>();
            buffer ="Port declaration: ";
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

void ElementaryCyclesSearch::dumpCyclesList(Netlist& netlist) {
    std::string buffer;
    auto s = cycles.size();
    if (!s)
        return;

    if (s == 1)
        buffer = ":\n";
    else
        buffer = "s:\n";
    std::cout << "Detected " << s << " combinatorial loop" << buffer;
    for (int i = 0; i < s; i++) {
        auto si = cycles[i].size();
        for (int j = 0; j < si; j++) {
            ElementaryCyclesSearch::getHierName(netlist.getNode(cycles[i][j]), buffer);
            std::cout <<buffer;
            if (j < si - 1) {
                std::cout << " => ";
            }
        }
        std::cout << "\n";
    }
}

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
bool ElementaryCyclesSearch::findCycles(ID_type v, ID_type s, std::vector<std::vector<ID_type>> adjList)  {
    bool f = false;
    this->stack.push_back(v);
    this->blocked[v] = true;

    for (int i = 0; i < adjList[v].size(); i++) {
        ID_type w = adjList[v][i];

        if (w == s) {
            CycleListType cycle;
            for (int j = 0; j < this->stack.size(); j++) {
                ID_type index = this->stack[j];
                cycle.push_back(index);
            }
            this->cycles.push_back(cycle);
            f = true;
        } else if (!this->blocked[w]) {
            if (this->findCycles(w, s, adjList)) {
                f = true;
            }
        }
    }

    if (f) {
        this->unblock(v);
    } else {
        for (int i = 0; i < adjList[v].size(); i++) {
            ID_type w = adjList[v][i];
            if (find(this->B[w].begin(), this->B[w].end(), v) == this->B[w].end()) {
                this->B[w].push_back(v);
            }
        }
    }

    this->stack.erase(remove(this->stack.begin(), this->stack.end(), v), this->stack.end());
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
