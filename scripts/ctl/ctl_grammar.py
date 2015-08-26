from pyparsing import Word, Literal, srange, Forward, Group, Or, OneOrMore

class CTLGrammar:
    left = Literal('(').suppress()
    right = Literal(')').suppress()
    comma = Literal(',').suppress()
    _in = Literal('in').suppress()
    leftCurly = Literal('{').suppress()
    rightCurly = Literal('}').suppress()
    leftSquare = Literal('{').suppress()
    rightSquare = Literal('}').suppress()
    
    neg = Literal('not')    
    ax = Literal('AX')
    ex = Literal('EX')
    af = Literal('AF')
    ef = Literal('EF')
    ag = Literal('AG')
    eg = Literal('EG')
    
    conj = Literal('and')    
    disj = Literal('or')
    impl = Literal('=>')
    au = Literal('AU')
    eu = Literal('EU')
        
    true = Literal('true')
    false = Literal('false')
    word = Word(srange("[A-Za-z0-9_]"))
                       
    unaryPropositionalOperator = neg
    binaryPropositionalOperator = conj | disj | impl
                       
    unaryCTLOperator = neg | ax | ex | af | ef | ag | eg
    binaryCTLOperator = conj | disj | impl | au | eu
    
    atomic = word | word + _in + leftCurly + Group(OneOrMore(word)) + rightCurly | word + _in + leftSquare + Group(OneOrMore(word)) + rightSquare
    
    policy = Forward()
    policy << Or([true, false, atomic, Group(left + unaryPropositionalOperator + policy + right), Group(left + binaryPropositionalOperator + policy + OneOrMore(policy) + right)])    
    
    ctlFormula = Forward()
    ctlFormula << Or([policy, Group(left + unaryCTLOperator + ctlFormula + right), Group(left + binaryCTLOperator + ctlFormula + ctlFormula + right)])
    
    req = Group(left + policy + comma + ctlFormula + right)
        
def parseRequirement(string):
    return CTLGrammar.req.parseString(string, parseAll = True)[0]

def parsePolicyFormula(string):
    return CTLGrammar.policy.parseString(string, parseAll = True)[0]

def parseCTLFormula(string):
    return CTLGrammar.ctlFormula.parseString(string, parseAll = True)[0]