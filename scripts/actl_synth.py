from ctl.ctl_grammar import parseCTLFormula

import networkx as nx
import re


resGraphFilename = '../kaba/simple.adj'
resGraph = nx.read_adjlist(resGraphFilename, create_using = nx.DiGraph())    
print 'Resource in the graph:', resGraph.nodes()  

m = {}


def check(s, f):
    print "check {} {}".format(s, f)
    if f not in m.keys():
        m[f] = {}
    if s in m[f].keys() and m[f][s] == 'true':
        return True
    if s in m[f].keys() and m[f][s] == 'false':
        return False
    m[f][s] = 'undef'  
    #print m
    if f[0] == 'AG':
        subformula = f[1]
        if not check(s, subformula):
            return False
        for e in resGraph.edges([s]):
            s1 = e[1]
            if s1 in m[f].keys():
                print 'already visited the state {} '.format(s1)
                if m[f][s1] == 'true':
                    m[f][s] = 'true'
                    return True
                continue
            if check(s1, f):
                pass
            else:
                print 'removing edge {} {}'.format(e[0], e[1])
                resGraph.remove_edge(s, s1)
        m[f][s] = 'true'
        return True
    elif f[0] == 'EF':
        assert re.match('^[a-zA-Z0-9_]+$', f[1])
        subformula = f[1]
        if check(s, subformula):
            m[f][s] = 'true'
            return True
        for e in resGraph.edges([s]):
            s1 = e[1]
            if s1 in m[f].keys():
                print 'already visited the state {} '.format(s1)
                if m[f][s1] == 'true':
                    m[f][s] = 'true'
                    return True
                continue
            if check(s1, f):
                m[f][s] = 'true'
                return True
        m[f][s] = 'false'
        return False
    elif re.match('^[a-zA-Z0-9_]+$', f[0]):
        print 'a proposition'
        m[f][s] = f[0] == s
        return f[0] == s
    elif f[0] == '!':
        assert re.match('^[a-zA-Z0-9_]+$', f[1])
        m[f][s] = f[1] != s
        return f[1] != s        
    else:
        print 'not supported' 
    
    return False

f = '(AG (EF cor))'
print f

print parseCTLFormula(f)

print check('out', parseCTLFormula(f))