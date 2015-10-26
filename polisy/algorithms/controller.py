from z3 import Bool, And, Solver, sat, unsat
import smt
from utils.helperMethods import INIT_RESOURCE, nodePathToEdgePath

def declareEdgeVars(resStructure):
    global EDGE_VARS
    for e in resStructure.edges():
        EDGE_VARS[e] = Bool(e[0] + '_' + e[1])


                     
def simplePathConditionFunction(resStructure, path, req):
    declareEdgeVars(resStructure)
    if len(path) < 2:
        return True
    edgePath = nodePathToEdgePath(resStructure, path)
    edgeVars = [EDGE_VARS[e] for e in edgePath]
    return And(edgeVars)

def restrictGraph(graph, req):    
    s = Solver()
    s.reset()
    s.add(smt.encodeFormula(graph, req, INIT_RESOURCE, simplePathConditionFunction))
    
    for e in graph.edges():
        if e[0] == e[1]:
            s.add(EDGE_VARS[e] == True)
   
    if s.check() == sat:
        model = s.model()
        restrictedGraph = graph.copy()
        for e in graph.edges():
            if model[EDGE_VARS[e]] is not None and model[EDGE_VARS[e]].sexpr() == 'false':
                restrictedGraph.remove_edge(e[0], e[1])
    else:
        return unsat
    
    return restrictedGraph