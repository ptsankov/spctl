import networkx
from networkx.classes.function import set_node_attributes
from synthesizer import conf

def setLogFile(filename):
    conf.outputFile = open(filename, 'w')

def closeLogFile():
    conf.outputFile.close()

def log(msg):
    print msg
    conf.outputFile.write(msg + '\n')

def nodePathToEdgePath(graph, nodePath):
    edgePath = []
    for i in range(0, len(nodePath)-1):
        for e in graph.edges_iter(nodePath[i]):
            if e[1] == nodePath[i+1]:
                edgePath.append(e)                 
    return edgePath

def readResourceStructure(structureFilename, resourceAttributesFilename):
    resourceStructure = networkx.read_adjlist(structureFilename, create_using = networkx.DiGraph())    
    log('Resources: ' + ', '.join(resourceStructure.nodes()))
    
    with open(resourceAttributesFilename) as f:
        resAttrsStr = f.readlines()
    resAttrsStr = [x.strip() for x in resAttrsStr]
    
    for resAttrs in resAttrsStr:
        resAttrMap = {}
        attrName = resAttrs.split('|')[0]
        attrPairs = resAttrs.split('|')[1]
        for attrPair in attrPairs.split(','):
            resId = attrPair.split(':')[0]
            attrVal = attrPair.split(':')[1]            
            resAttrMap[resId] = attrVal
        set_node_attributes(resourceStructure, attrName, resAttrMap)
    resAttrMap = {}
    for n in resourceStructure.nodes():
        resAttrMap[n] = n
    set_node_attributes(resourceStructure, 'room_id', resAttrMap)
    return resourceStructure