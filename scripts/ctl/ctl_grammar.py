from pyparsing import Word, Literal, srange, Forward, Group, Or, OneOrMore

class CTLGrammar:
    left = Literal('(').suppress()
    right = Literal(')').suppress()
    comma = Literal(',').suppress()
    
    
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
    proposition = Word(srange("[A-Za-z0-9]"))
                       
    unaryPropositionalOperator = neg
    binaryPropositionalOperator = conj | disj | impl
                       
    unaryCTLOperator = neg | ax | ex | af | ef | ag | eg
    binaryCTLOperator = conj | disj | impl | au | eu
    
    propositionalFormula = Forward()
    propositionalFormula << Or([true, false, proposition, Group(left + unaryPropositionalOperator + propositionalFormula + right), Group(left + binaryPropositionalOperator + propositionalFormula + OneOrMore(propositionalFormula) + right)])    
    
    ctlFormula = Forward()
    ctlFormula << Or([propositionalFormula, Group(left + unaryCTLOperator + ctlFormula + right), Group(left + binaryCTLOperator + ctlFormula + ctlFormula + right)])
    
    req = Group(left + propositionalFormula + comma + ctlFormula + right)
        
def parseRequirement(string):
    return CTLGrammar.req.parseString(string, parseAll = True)[0]

def parsePropositionalFormula(string):
    return CTLGrammar.propositionalFormula.parseString(string, parseAll = True)[0]

def parseCTLFormula(string):
    return CTLGrammar.ctlFormula.parseString(string, parseAll = True)[0]