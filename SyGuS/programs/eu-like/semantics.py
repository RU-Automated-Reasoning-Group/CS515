from z3 import parse_smt2_string

def ite(arg1, arg2, arg3):
    if arg1:
        return arg2
    else:
        return arg3

opmap = {
    '+': lambda x, y, z: x + y,
    '-': lambda x, y, z: x - y,
    '*': lambda x, y, z: x * y,
    'div': lambda x, y, z: x // y,
    'mod': lambda x, y, z: x % y,
    'ite': ite,
    'and': lambda x, y, z: x and y,
    'or': lambda x, y, z: x or y,
    '=>': lambda x, y, z: (not x) or y,
    'xor': lambda x, y, z: x != y,
    'xnor': lambda x, y, z: x == y,
    'nand': lambda x, y, z: not (x and y),
    'nor': lambda x, y, z: not (x or y),
    'iff': lambda x, y, z: x == y,
    'not': lambda x, y, z: not x,
    '=': lambda x, y, z: x == y,
    '<=': lambda x, y, z: x <= y,
    '<': lambda x, y, z: x < y,
    '>=': lambda x, y, z: x >= y,
    '>': lambda x, y, z: x > y
}

class Func:
    def __init__(self, name, arglist, typelist, retty, expr = None):
        self.name = name
        self.arglist = arglist
        self.typelist = typelist
        self.argtymap = {}
        for a, t in zip(arglist, typelist):
            self.argtymap[a] = t
        self.retty = retty
        self.expr = expr

    def eval(self, outersymtab, realargs):
        symtab = {}
        for a, r in zip(self.arglist, realargs):
            symtab[a] = r.eval(outersymtab)
        return self.expr.eval(symtab)

    def __str__(self):
        ret = '(define-fun ' + self.name + ' ('
        for i in range(len(self.arglist)):
            if i != 0:
                ret += ' '
            ret += '(' + self.arglist[i] + ' ' + self.typelist[i] + ')'
        ret += ') ' + self.retty + ' '
        if self.expr is None:
            if self.retty == 'Int':
                ret += '0)'
            else:
                ret += 'false)'
        else:
            ret += str(self.expr) + ')'
        return ret

    def declarestr(self):
        ret = '(declare-fun ' + self.name + ' ('
        for i in range(len(self.typelist)):
            if i != 0:
                ret += ' '
            ret += self.typelist[i]
        ret += ') ' + self.retty + ')'
        return ret

    def getargtype(self, arg):
        return self.argtymap[arg]

class Expr:
    productions = None
    def __init__(self, op, arg1 = None, arg2 = None, arg3 = None):
        assert self.productions is not None
        productions = self.productions
        self.op = op

        if isinstance(op, int):
            self.size = 1
            self.hole = 0
        elif isinstance(op, bool):
            self.size = 1
            self.hole = 0
        elif isinstance(op, Func):
            self.size = 1
            self.hole = 0 # no need since this will only be used in checker
        elif op == 'ite':
            self.size = 1 + arg1.size + arg2.size + arg3.size
            self.hole = arg1.hole + arg2.hole + arg3.hole
        elif op == 'not':
            self.size = 1 + arg1.size
            self.hole = arg1.hole
        elif op in productions: # non terminal
            self.size = 1
            self.hole = 1
        elif arg1 is not None: # binary
            self.size = 1 + arg1.size + arg2.size
            self.hole = arg1.hole + arg2.hole
        else: # var
            self.size = 1
            self.hole = 0

        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3

    def isconst(self):
        if isinstance(self.op, int) or isinstance(self.op, bool):
            return True
        return False

    def eval(self, symtab):
        # assert self.hole != 0
        if isinstance(self.op, int):
            return self.op
        if isinstance(self.op, bool):
            return self.op
        if isinstance(self.op, Func):
            return self.op.eval(symtab, self.arg1)
        if self.arg3 is not None:
            return opmap[self.op](self.arg1.eval(symtab), self.arg2.eval(symtab), self.arg3.eval(symtab))
        if self.arg2 is not None:
            return opmap[self.op](self.arg1.eval(symtab), self.arg2.eval(symtab), None)
        if self.arg1 is not None:
            return opmap[self.op](self.arg1.eval(symtab), None, None)
        return symtab[self.op]

    def __lt__(self, other):
        if self.hole == 0 and other.hole != 0:
            return True
        if self.size == other.size:
            return self.hole < other.hole
        return self.size < other.size

    def __eq__(self, other):
        if other == None:
            return False
        # only one function?
        if isinstance(self.op, Func) and isinstance(other.op, Func):
            return True
        if self.op == other.op:
            return self.arg1 == other.arg1 and self.arg2 == other.arg2 and self.arg3 == other.arg3
        return False

    def extend(self):
        productions = self.productions
        if self.hole == 0:
            return []

        if self.op == 'ite':
            r1 = list(filter(lambda e: not e.arg1.isconst(),
                             map(lambda x: Expr('ite', x, self.arg2, self.arg3), self.arg1.extend())))
            r2 = list(filter(lambda e: not str(e.arg2) == str(e.arg3),
                             map(lambda x: Expr('ite', self.arg1, x, self.arg3), self.arg2.extend())))
            r3 = list(filter(lambda e: not str(e.arg2) == str(e.arg3),
                             map(lambda x: Expr('ite', self.arg1, self.arg2, x), self.arg3.extend())))
            return r1 + r2 + r3
        elif self.op == 'not':
            return list(filter(lambda e: (not (e.arg1.isconst())) and e.op != 'not',
                               map(lambda x: Expr('not', x), self.arg1.extend())))
        elif self.op in productions:
            ret = []
            for p in productions[self.op]:
                if not isinstance(p, list):
                    ret.append(Expr(p))
                elif p[0] == 'Int':
                    ret.append(Expr(int(p[1])))
                elif p[0] == 'Bool':
                    ret.append(Expr(bool(p[1])))
                elif p[0] == 'ite':
                    ret.append(Expr('ite',
                                    Expr(p[1]),
                                    Expr(p[2]),
                                    Expr(p[3])))
                elif p[0] == 'not':
                    ret.append(Expr('not',
                                    Expr(p[1])))
                else:
                    ret.append(Expr(p[0], Expr(p[1]), Expr(p[2])))
            return ret
        elif self.arg1 is not None:
            r1 = filter(lambda e: not (e.arg1.isconst() and e.arg2.isconst()),
                             map(lambda x: Expr(self.op, x, self.arg2), self.arg1.extend()))
            r2 = filter(lambda e: not (e.arg1.isconst() and e.arg2.isconst()),
                             map(lambda x: Expr(self.op, self.arg1, x), self.arg2.extend()))
            if self.op in ['=', 'and', 'or', 'xor', 'xnor', 'nand', 'nor', '+', '*']:
                r1 = filter(lambda e: str(e.arg1) < str(e.arg2), r1)
                r2 = filter(lambda e: str(e.arg1) < str(e.arg2), r2)
            if self.op in ['<=', '>=', '-', 'div', 'mod']:
                r1 = filter(lambda e: str(e.arg1) != str(e.arg2), r1)
                r2 = filter(lambda e: str(e.arg1) != str(e.arg2), r2)
            if self.op in ['+', '-', '*', 'div', 'mod']:
                r1 = filter(lambda e: (not isinstance(e.arg2.op, int) or e.arg2.op != 0), r1)
                r2 = filter(lambda e: (not isinstance(e.arg2.op, int) or e.arg2.op != 0), r2)
            if self.op in ['+', '*', 'div', 'mod']:
                r1 = filter(lambda e: (not isinstance(e.arg1.op, int) or e.arg1.op != 0), r1)
                r2 = filter(lambda e: (not isinstance(e.arg1.op, int) or e.arg1.op != 0), r2)

            def doublec(e):
                if isinstance(e.op, int):
                    return 1
                if e.op in ['+', '-']:
                    t = doublec(e.arg1)
                    if t >= 2:
                        return t
                    return t + doublec(e.arg2)
                return 0
            def triplec(e):
                if e.op in ['+', '-']:
                    l = doublec(e.arg1) + doublec(e.arg2)
                    if l >= 2:
                        return True
                return False
            if self.size >= 5:
                r1 = filter(lambda e: not triplec(e), r1)
                r2 = filter(lambda e: not triplec(e), r2)

            return list(r1) + list(r2)
        else:
            assert False

    def __str__(self):
        op = self.op
        if isinstance(op, int):
            return str(op)
        elif isinstance(op, bool):
            if op:
                return 'true'
            else:
                return 'false'
        elif isinstance(op, Func):
            ret = '(' + self.op.name
            for arg in self.arg1:
                ret += ' ' + str(arg)
            ret += ')'
            return ret
        elif op == 'ite':
            return '(ite ' + str(self.arg1) + ' ' + str(self.arg2) + ' ' + str(self.arg3) + ')'
        elif op == 'not':
            return '(not ' + str(self.arg1) + ')'
        elif op in self.productions: # non terminal
            return op
        elif self.arg1 is not None: # binary
            return '(' + self.op + ' ' + str(self.arg1) + ' ' + str(self.arg2) + ')'
        else: # var
            return op

def exprFromList(l, funcprotos):
    if isinstance(l, list):
        if l[0] == 'Int':
            return Expr(int(l[1]))
        if l[0] == 'Bool':
            return Expr(bool(l[1]))
        if l[0] in funcprotos:
            args = list(map(lambda l1: exprFromList(l1, funcprotos), l[1:]))
            return Expr(funcprotos[l[0]], args)
        arg1 = arg2 = arg3 = None
        if len(l) >= 2:
            arg1 = exprFromList(l[1], funcprotos)
        if len(l) >= 3:
            arg2 = exprFromList(l[2], funcprotos)
        if len(l) >= 4:
            arg3 = exprFromList(l[3], funcprotos)
        return Expr(l[0], arg1, arg2, arg3)
    elif isinstance(l, tuple):
        if l[0] == 'Int':
            return Expr(int(l[1]))
        if l[0] == 'Bool':
            return Expr(bool(l[1]))
    else:
        return Expr(l)


def exprsToZ3(exprs, vartab, func=None, defined=False):
    smtstr = ''
    if func is not None:
        if defined:
            smtstr += str(func)
        else:
            smtstr += func.declarestr()
        smtstr += '\n'
    for s in map(str, exprs):
        smtstr += '(assert '
        smtstr += s
        smtstr += ')\n'
    return parse_smt2_string(smtstr, decls=vartab)


def exprToList(expr: Expr):
    if isinstance(expr.op, int):
        return ('Int', expr.op)
    if isinstance(expr.op, bool):
        return ('Bool', expr.op)
    if isinstance(expr.op, Func):
        args = list(map(exprToList, expr.arg1))
        ret = [expr.op.name]
        ret.extend(args)
        return ret
    if expr.arg1 is None:
        return expr.op
    ret = [expr.op, exprToList(expr.arg1)]
    if expr.arg2 is not None:
        ret.append(exprToList(expr.arg2))
    if expr.arg3 is not None:
        ret.append(exprToList(expr.arg3))
    return ret

def main():
    Expr.productions = {}
    fb = Func('func', ['x','y'], ['Int', 'Int'], 'Int')
    print(fb)
    f = Func('func', ['x','y'], ['Int', 'Int'], 'Int', Expr('+', Expr('x'), Expr('y')))
    print(f)
    e = Expr(f, [Expr('z'), Expr('a')])
    print(e)
    print(e.eval({'z': 1, 'a': 2}))
    e1 = exprFromList(['func', 'z', ['+', 'z', 'a']], {'func': f})
    print(e1)
    print(e1.eval({'z': 1, 'a': 2}))
    print(e1.eval({'z': 2, 'a': 1}))

if __name__ == '__main__':
    main()
