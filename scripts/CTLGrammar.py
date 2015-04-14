from pyparsing import Word, Literal, srange, ZeroOrMore, Optional, OneOrMore, Forward, Group, Or

class CTLGrammar:
    left = Literal('(').suppress()
    right = Literal(')').suppress()
    
    
    neg = Literal('!')    
    ax = Literal('AX')
    ex = Literal('EX')
    af = Literal('AF')
    ef = Literal('EF')
    ag = Literal('AG')
    eg = Literal('EG')
    
    conj = Literal('&')
    disj = Literal('|')
    impl = Literal('->')
    au = Literal('AU')
    eu = Literal('EU')
        
    true = Literal('true')
    false = Literal('false')
    proposition = Word(srange("[a-z]"))
                       
    unaryOperator = neg | ax | ex | af | ef | ag | eg
    binaryOperator = conj | disj | impl | au | eu    
    
    formula = Forward()
    formula << Or([true, false, proposition, Group(left + unaryOperator + formula + right), Group(left + binaryOperator + formula + formula + right)])
        
def parseCTLFormula(string):
    return CTLGrammar.formula.parseString(string, parseAll = True)[0]