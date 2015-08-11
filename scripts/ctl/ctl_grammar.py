from pyparsing import Word, Literal, srange, Forward, Group, Or

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
    proposition = Word(srange("[a-z0-9]"))
                       
    unaryPropositionalOperator = neg
    binaryPropositionalOperator = conj | disj | impl
                       
    unaryCTLOperator = neg | ax | ex | af | ef | ag | eg
    binaryCTLOperator = conj | disj | impl | au | eu
    
    propositionalFormula = Forward()
    propositionalFormula << Or([true, false, proposition, Group(left + unaryPropositionalOperator + propositionalFormula + right), Group(left + binaryPropositionalOperator + propositionalFormula + propositionalFormula + right)])    
    
    ctlFormula = Forward()
    ctlFormula << Or([propositionalFormula, Group(left + unaryCTLOperator + ctlFormula + right), Group(left + binaryCTLOperator + ctlFormula + ctlFormula + right)])
    
    req = Group(left + propositionalFormula + comma + ctlFormula + right)
        
def parseRequirement(string):
    return CTLGrammar.req.parseString(string, parseAll = True)[0]