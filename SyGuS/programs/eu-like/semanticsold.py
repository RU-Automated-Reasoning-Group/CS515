'''
class Expr:
    canextend = False
    tyname = None
    def eval(self):
        return None
    def extend(self):
        return []

class BooleanExpr(Expr):
    tyname = 'Bool'
    pass

class BooleanConst(BooleanExpr):
    def __init__(self, b):
        assert isinstance(b, bool)
        self.b = b

    def eval(self):
        return self.b

    def __str__(self):
        if self.b:
            return 'true'
        else:
            return 'false'

class BooleanVar(BooleanExpr):
    def __init__(self, name):
        self.name = name
        self.value = None

    def assign(self, b):
        assert isinstance(b, bool)
        self.value = b

    def eval(self):
        assert self.value is not None
        return self.value

    def __str__(self):
        return self.name


class BooleanIte(BooleanExpr):
    def __init__(self, b, t, e):
        assert isinstance(b, BooleanExpr)
        assert isinstance(t, BooleanExpr)
        assert isinstance(e, BooleanExpr)
        self.b = b
        self.t = t
        self.e = e

    def eval(self):
        if self.b.eval():
            return self.t.eval()
        else:
            return self.e.eval()

    def __str__(self):
        return '(ite ' + str(self.b) + ' ' + str(self.t) + ' ' + str(self.e) + ')'

    def extend(self):
        if not self.canextend:
            return []
        ret = list(map(lambda b: BooleanIte(b, self.t, self.e), self.b.extend())) + \
              list(map(lambda t: BooleanIte(self.b, t, self.e), self.t.extend())) + \
              list(map(lambda e: BooleanIte(self.b, self.t, e), self.e.extend()))
        if ret == []:
            self.canextend = False
        return ret

class BooleanUnaryExpr(BooleanExpr):
    def __init__(self, arg, opname):
        assert isinstance(arg, BooleanExpr)
        self.arg = arg
        self.opname = opname

    def __str__(self):
        return '(' + self.opname + ' ' + str(self.arg) + ')'


class NotExpr(BooleanUnaryExpr):
    def __init__(self, arg):
        super().__init__(arg, 'not')

    def eval(self):
        return not self.arg.eval()

    def extend(self):
        return list(map(lambda a: NotExpr(a), self.arg.extend()))

class BooleanBinaryExpr(BooleanExpr):
    def __init__(self, left, right, opname):
        assert isinstance(left, BooleanExpr)
        assert isinstance(right, BooleanExpr)
        self.left = left
        self.right = right
        self.opname = opname

    def __str__(self):
        return '( ' + self.opname + ' ' + str(self.left) + ' ' + str(self.right) + ' )'

class AndExpr(BooleanBinaryExpr):
    def __init__(self, left, right):
        super().__init__(left, right, 'and')

    def eval(self):
        return self.left.eval() and self.right.eval()

    def extend(self):
        ret = list(map(lambda l: AndExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: AndExpr(self.left, r), self.left.extend()))
        return ret

class OrExpr(BooleanBinaryExpr):
    def __init__(self, left, right):
        super().__init__(left, right, 'or')

    def eval(self):
        return self.left.eval() or self.right.eval()

    def extend(self):
        ret = list(map(lambda l: OrExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: OrExpr(self.left, r), self.left.extend()))
        return ret


class ImplyExpr(BooleanBinaryExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '=>')

    def eval(self):
        return (not self.left.eval()) or self.right.eval()

    def extend(self):
        ret = list(map(lambda l: ImplyExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: ImplyExpr(self.left, r), self.left.extend()))
        return ret


class IntExpr(Expr):
    tyname = 'Int'
    pass


class IntConst(IntExpr):
    def __init__(self, n):
        assert isinstance(n, int)
        self.n = n

    def eval(self):
        return self.n

    def __str__(self):
        return str(self.n)


class IntVar(IntExpr):
    def __init__(self, name):
        self.name = name
        self.value = None

    def assign(self, n):
        assert isinstance(n, int)
        self.value = n

    def eval(self):
        assert self.value is not None
        return self.value

    def __str__(self):
        return self.name


class IntCmpExpr(BooleanExpr):
    def __init__(self, left, right, opname):
        assert isinstance(left, IntExpr)
        assert isinstance(right, IntExpr)
        self.left = left
        self.right = right
        self.opname = opname

    def __str__(self):
        return '(' + self.opname + ' ' + str(self.left) + ' ' + str(self.right) + ')'

class IntETExpr(IntCmpExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '=')

    def eval(self):
        return self.left.eval() == self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntETExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntETExpr(self.left, r), self.left.extend()))
        return ret


class IntLTExpr(IntCmpExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '<')

    def eval(self):
        return self.left.eval() < self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntLTExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntLTExpr(self.left, r), self.left.extend()))
        return ret

class IntLTEExpr(IntCmpExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '<=')

    def eval(self):
        return self.left.eval() <= self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntLTEExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntLTEExpr(self.left, r), self.left.extend()))
        return ret

class IntGTExpr(IntCmpExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '>')

    def eval(self):
        return self.left.eval() > self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntGTExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntGTExpr(self.left, r), self.left.extend()))
        return ret

class IntGTEExpr(IntCmpExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '>=')

    def eval(self):
        return self.left.eval() >= self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntGTEExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntGTEExpr(self.left, r), self.left.extend()))
        return ret

class IntArithExpr(IntExpr):
    def __init__(self, left, right, opname):
        assert isinstance(left, IntExpr)
        assert isinstance(right, IntExpr)
        self.left = left
        self.right = right
        self.opname = opname

    def __str__(self):
        return '(' + self.opname + ' ' + str(self.left) + ' ' + str(self.right) + ')'


class IntPlusExpr(IntArithExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '+')

    def eval(self):
        return self.left.eval() + self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntPlusExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntPlusExpr(self.left, r), self.left.extend()))
        return ret


class IntMinusExpr(IntArithExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '-')

    def eval(self):
        return self.left.eval() - self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntMinusExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntMinusExpr(self.left, r), self.left.extend()))
        return ret


class IntTimesExpr(IntArithExpr):
    def __init__(self, left, right):
        super().__init__(left, right, '*')

    def eval(self):
        return self.left.eval() * self.left.eval()

    def extend(self):
        ret = list(map(lambda l: IntTimesExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntTimesExpr(self.left, r), self.left.extend()))
        return ret


class IntDivExpr(IntArithExpr):
    def __init__(self, left, right):
        super().__init__(left, right, 'div')

    def eval(self):
        return self.left.eval() // self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntDivExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntDivExpr(self.left, r), self.left.extend()))
        return ret


class IntModExpr(IntArithExpr):
    def __init__(self, left, right):
        super().__init__(left, right, 'mod')

    def eval(self):
        return self.left.eval() % self.right.eval()

    def extend(self):
        ret = list(map(lambda l: IntModExpr(l, self.right), self.right.extend())) + \
              list(map(lambda r: IntModExpr(self.left, r), self.left.extend()))
        return ret


class IntIte(IntExpr):
    def __init__(self, b, t, e):
        assert isinstance(b, BooleanExpr)
        assert isinstance(t, IntExpr)
        assert isinstance(e, IntExpr)
        self.b = b
        self.t = t
        self.e = e

    def eval(self):
        if self.b.eval():
            return self.t.eval()
        else:
            return self.e.eval()

    def __str__(self):
        return '(ite ' + str(self.b) + ' ' + str(self.t) + ' ' + str(self.e) + ')'

    def extend(self):
        if not self.canextend:
            return []
        ret = list(map(lambda b: IntIte(b, self.t, self.e), self.b.extend())) + \
              list(map(lambda t: IntIte(self.b, t, self.e), self.t.extend())) + \
              list(map(lambda e: IntIte(self.b, self.t, e), self.e.extend()))
        if ret == []:
            self.canextend = False
        return ret


class Function:
    def __init__(self, name, argslist, expr):
        assert all(map(lambda x: isinstance(x, BooleanVar) or isinstance(x, IntVar), argslist))
        self.name = name
        self.argslist = argslist
        self.expr = expr
        self.retty = expr.tyname

    def apply(self, realargslist):
        assert len(self.argslist) == len(realargslist)
        for r, a in zip(realargslist, self.argslist):
            a.assign(r)
        return self.expr.eval()

    def __str__(self):
        argliststr = ''
        for arg in self.argslist:
            if argliststr != '':
                argliststr += ' '
            argliststr += '('
            argliststr += arg.name
            argliststr += ' '
            argliststr += arg.tyname
            argliststr += ')'
        return '(define-fun ' + self.name + ' (' + argliststr + ') ' + self.retty + ' ' + str(self.expr) + ')'


class IntFunction(Function):
    def __init__(self, name, argslist, expr):
        assert isinstance(expr, IntExpr)
        super().__init__(name, argslist, expr)


class BoolFunction(Function):
    def __init__(self, name, argslist, expr):
        assert isinstance(expr, BooleanExpr)
        super().__init__(name, argslist, expr)


class IntHole(IntExpr):
    pass


class BooleanHole(BooleanExpr):
    pass


def main():
    arg1 = IntVar('a')
    expr1 = IntPlusExpr(IntConst(1), arg1)
    f = IntFunction('func', [arg1], expr1)
    print(f.apply([10]))
    print(f)

if __name__ == '__main__':
    main()

'''