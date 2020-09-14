from z3 import Int, Bool

from semantics.semantics import Func


class SemChecker:
    def __init__(self, funcproto, constraint, inputlist, inputtylist):
        self.funcproto = funcproto
        self.inputlist = inputlist
        self.inputtylist = inputtylist
        self.constraint = constraint

        self.usage = []

        for u in self.searchconstraint(self.constraint):
            distinct = True
            for oldu in self.usage:
                eq = True
                for k in u:
                    if oldu[k] != u[k]:
                        eq = False
                        break
                if eq:
                    distinct = False
            if len(self.usage) == 0:
                distinct = True
            if distinct:
                self.usage.append(u)

    def searchconstraint(self, constraintlist):
        ret = []
        op = constraintlist.op
        if isinstance(op, Func):
            ret1 = []
            for a in constraintlist.arg1:
                ret1 += self.searchconstraint(a)
            if len(ret1) == 0:
                nxtret = {}
                for a, r in zip(self.funcproto.arglist, constraintlist.arg1):
                    nxtret[a] = r
                ret.append(nxtret)
            else:
                ret.extend(ret1)
            return ret
        elif isinstance(op, int) or isinstance(op, bool):
            return []
        if constraintlist.arg1 is not None:
            ret.extend(self.searchconstraint(constraintlist.arg1))
        if constraintlist.arg2 is not None:
            ret.extend(self.searchconstraint(constraintlist.arg2))
        if constraintlist.arg3 is not None:
            ret.extend(self.searchconstraint(constraintlist.arg3))
        return ret


    def getSymtab(self, outersymtab):
        ret = []
        for t in self.usage:
            nsym = {}
            for k in t:
                nsym[k] = t[k].eval(outersymtab)
            ret.append(nsym)
        return ret


    def check(self, expr, symtab):
        self.funcproto.expr = expr
        return self.constraint.eval(symtab)

    def getz3vartab(self):
        def DeclareVar(sort, name):
            if sort == "Int":
                return Int(name)
            if sort == 'Bool':
                return Bool(name)

        vartab = {}
        for i, t in zip(self.inputlist, self.inputtylist):
            vartab[i] = DeclareVar(t, i)
        return vartab
