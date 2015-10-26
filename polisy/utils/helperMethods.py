import os
INIT_RESOURCE = 'out'

def setLogFile(filename):
    global outputFile
    assert os.path.isfile(filename)
    outputFile = open(filename, 'w')

def log(msg):
    print msg
    outputFile.write(msg + '\n')

def nodePathToEdgePath(graph, nodePath):
    edgePath = []
    for i in range(0, len(nodePath)-1):
        for e in graph.edges_iter(nodePath[i]):
            if e[1] == nodePath[i+1]:
                edgePath.append(e)                 
    return edgePath