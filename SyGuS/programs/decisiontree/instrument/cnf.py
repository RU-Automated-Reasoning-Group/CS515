from z3 import *

from semantics.semantics import Expr, exprsToZ3


def eliminateOp(expr):
    if expr.op == '=>':
        return Expr('or',
                    Expr('not',
                         eliminateOp(expr.arg1)),
                    eliminateOp(expr.arg2))
    if expr.op == 'xor':
        return Expr('or',
                    Expr('and',
                         Expr('not',
                              eliminateOp(expr.arg1)),
                         eliminateOp(expr.arg2)),
                    Expr('and',
                         eliminateOp(expr.arg1),
                         Expr('not',
                              eliminateOp(expr.arg2))))
    if expr.op in ['xnor', 'iff']:
        return Expr('or',
                    Expr('and',
                         eliminateOp(expr.arg1),
                         eliminateOp(expr.arg2)),
                    Expr('and',
                         Expr('not',
                              eliminateOp(expr.arg1)),
                         Expr('not',
                              eliminateOp(expr.arg2))))
    if expr.op == 'nand':
        return Expr('not',
                    Expr('and',
                         eliminateOp(expr.arg1),
                         eliminateOp(expr.arg2)))
    if expr.op == 'nor':
        return Expr('not',
                    Expr('or',
                         eliminateOp(expr.arg1),
                         eliminateOp(expr.arg2)))
    if expr.op == 'ite':
        return Expr('or',
                    Expr('and',
                         eliminateOp(expr.arg1),
                         eliminateOp(expr.arg2)),
                    Expr('and',
                         Expr('not',
                              eliminateOp(expr.arg1)),
                         eliminateOp(expr.arg3)))
    return expr


def putInNot(expr):
    if expr.op == 'not':
        if expr.arg1.op == 'not':
            return putInNot(expr.arg1.arg1)
        if expr.arg1.op == 'and':
            return Expr('or',
                        putInNot(Expr('not', expr.arg1.arg1)),
                        putInNot(Expr('not', expr.arg1.arg2)))
        if expr.arg1.op == 'or':
            return Expr('and',
                        putInNot(Expr('not', expr.arg1.arg1)),
                        putInNot(Expr('not', expr.arg1.arg2)))
    if expr.op == 'and':
        return Expr('and',
                    putInNot(expr.arg1),
                    putInNot(expr.arg2))
    if expr.op == 'or':
        return Expr('or',
                    putInNot(expr.arg1),
                    putInNot(expr.arg2))
    return expr


def distribution(expr):
    # not in inner so no need to consider it
    if expr.op == 'and':
        return Expr('and', distribution(expr.arg1), distribution(expr.arg2))
    if expr.op == 'or':
        # distribution left
        if expr.arg1.op == 'and':
            rd = distribution(expr.arg2)
            return Expr('and',
                        distribution(Expr('or',
                                          expr.arg1.arg1,
                                          rd)),
                        distribution(Expr('or',
                                          expr.arg1.arg2,
                                          rd)))
        if expr.arg2.op == 'and':
            ld = distribution(expr.arg1)
            return Expr('and',
                        distribution(Expr('or',
                                          ld,
                                          expr.arg2.arg1)),
                        distribution(Expr('or',
                                          ld,
                                          expr.arg2.arg2)))
    return expr


def toRawCNF(expr):
    expr = eliminateOp(expr)
    expr = putInNot(expr)
    expr = distribution(expr)
    return expr


def getCNFclause(expr):
    if expr.op == 'and':
        return getCNFclause(expr.arg1) + getCNFclause(expr.arg2)
    else:
        return [expr]


def trivial(expr1, vartab, func):
    spec = exprsToZ3([expr1], vartab, func)
    spec = Not(spec[0])
    solver = Solver()
    solver.add(spec)
    res = solver.check()
    if res == unsat:
        return True
    else:
        return False


def clauseeq(expr1, expr2, vartab, func):
    spec = exprsToZ3([expr1, expr2], vartab, func)
    spec = And(Implies(spec[0], spec[1]), Implies(spec[1], spec[0]))
    solver = Solver()
    solver.add(Not(spec))
    res = solver.check()
    if res == unsat:
        return True
    else:
        return False


def filterclause(exprlist, vartab, func):
    l1 = []
    for e in exprlist:
        if not trivial(e, vartab, func):
            ok = True
            for i in l1:
                if clauseeq(e, i, vartab, func):
                    ok = False
                    break
            if ok:
                l1.append(e)
    return l1


def assemblyCNF(exprlist):
    if len(exprlist) == 0:
        return Expr(True)
    expr = exprlist[0]
    for i in range(1, len(exprlist)):
        expr = Expr('and', expr, exprlist[i])
    return expr


def buildCNF(expr, vartab, func):
    rawcnf = toRawCNF(expr)
    rawlist = getCNFclause(rawcnf)
    filteredlist = filterclause(rawlist, vartab, func)
    return assemblyCNF(filteredlist)


def main():
    Expr.productions = []
    expr = Expr('iff', Expr('=>', Expr('p'), Expr('q')), Expr('r'))
    cnfexpr = toRawCNF(expr)
    print(cnfexpr)
    # print(toCNF(expr))
    c = getCNFclause(cnfexpr)
    vartab = {'p': Bool('p'), 'q': Bool('q'), 'r': Bool('r')}
    func = None
    print(clauseeq(Expr('q'), Expr('p'), {'p': Bool('p'), 'q': Bool('q'), 'r': Bool('r')}, None))
    print(clauseeq(Expr('q'), Expr('p'), {'p': Bool('p'), 'q': Bool('q'), 'r': Bool('r')}, None))
    for s in filterclause(c, vartab, func):
        print(s)
    print(buildCNF(expr, vartab, func))



if __name__ == '__main__':
    main()
