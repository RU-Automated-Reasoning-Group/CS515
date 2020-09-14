from z3 import *

import sexp
import translator
from cnf import buildCNF, getCNFclause
from semantics import Func, Expr, exprFromList, exprToList
from semanticschecker import SemChecker


def _get_inputlists(bmdlvarlist):
    inputlist = []
    inputtylist = []
    inputmap = {}
    for expr in bmdlvarlist:
        inputlist.append(expr[1])
        inputtylist.append(expr[2])
        inputmap[expr[1]] = expr[2]
    return inputlist, inputtylist, inputmap


def _get_constraintlist(bmconstraintlist, functionProto):
    constraintlist = []
    for expr in bmconstraintlist:
        if isinstance(expr[1], list):
            constraintlist.append(exprFromList(expr[1], {functionProto.name: functionProto}))
        else:
            constraintlist.append(exprFromList(expr[1:], {functionProto.name: functionProto}))
    return constraintlist


def _constraintlist2conjunction(constraintlist):
    if len(constraintlist) == 0:
        return Expr(True)
    constraint = constraintlist[0]
    for c in constraintlist[1:]:
        constraint = Expr('and', constraint, c)
    return constraint


def _define_z3_var(sort, name):
    if sort == 'Int':
        return Int(name)
    if sort == 'Bool':
        return Bool(name)


def _getvartab(inputlist, inputtylist):
    vartab = {}
    for i, t in zip(inputlist, inputtylist):
        vartab[i] = _define_z3_var(t, i)
    return vartab


def _getusedvar(constraint):
    used = set()
    if isinstance(constraint.op, Func):
        for a in constraint.arg1:
            used = used.union(_getusedvar(a))
        return used
    elif isinstance(constraint.op, int):
        return set()
    elif isinstance(constraint.op, bool):
        return set()
    elif constraint.op not in ['+', '-', '*', 'div', 'mod', 'ite', 'and', 'or',
                               '=>', 'xor', 'xnor', 'nand', 'nor', 'iff', 'not',
                               '=', '>=', '>', '<=', '<']:
        return {constraint.op}
    if constraint.arg1 is not None:
        used = used.union(_getusedvar(constraint.arg1))
    if constraint.arg2 is not None:
        used = used.union(_getusedvar(constraint.arg2))
    if constraint.arg3 is not None:
        used = used.union(_getusedvar(constraint.arg3))
    return used


def _instrument_add_suffix(constraint, inputmap):
    if constraint is None:
        return None
    if isinstance(constraint.op, Func):
        arg1 = list(map(lambda x: _instrument_add_suffix(x, inputmap), constraint.arg1))
        return Expr(constraint.op, arg1)
    if isinstance(constraint.op, int):
        return constraint
    if isinstance(constraint.op, bool):
        return constraint
    if constraint.op not in ['+', '-', '*', 'div', 'mod', 'ite', 'and', 'or',
                             '=>', 'xor', 'xnor', 'nand', 'nor', 'iff', 'not',
                             '=', '>=', '>', '<=', '<']:
        return Expr(constraint.op + '__' + inputmap[constraint.op])
    return Expr(constraint.op,
                _instrument_add_suffix(constraint.arg1, inputmap),
                _instrument_add_suffix(constraint.arg2, inputmap),
                _instrument_add_suffix(constraint.arg3, inputmap))


def _instrument_have_func(expr):
    if expr == None:
        return False
    if isinstance(expr.op, int):
        return False
    if isinstance(expr.op, bool):
        return False
    if isinstance(expr.op, Func):
        return True
    return _instrument_have_func(expr.arg1) or \
           _instrument_have_func(expr.arg2) or \
           _instrument_have_func(expr.arg3)


def _instrument_split_constraint(constraint):
    # only or not
    if constraint.op == 'or':
        lwf, lnf = _instrument_split_constraint(constraint.arg1)
        rwf, rnf = _instrument_split_constraint(constraint.arg2)
        return lwf + rwf, lnf + rnf
    if constraint.op == 'not':
        # innermost
        if _instrument_have_func(constraint.arg1):
            return [constraint], []
        else:
            return [], [constraint]
    else:
        if _instrument_have_func(constraint):
            return [constraint], []
        else:
            return [], [constraint]


def _do_instrument_constraint(clause, funcproto):
    if clause == None:
        return None, []
    assert isinstance(funcproto, Func)
    guards = []
    if clause.op == 'not':
        return Expr('not', _do_instrument_constraint(clause.op, funcproto))
    if isinstance(clause.op, Func):
        assert clause.op.name == funcproto.name
        arglist, guardlist = zip(*list(map(lambda x: _do_instrument_constraint(x, funcproto), clause.arg1)))
        for g in guardlist:
            guards.extend(g)
        for x, a in zip(funcproto.arglist, arglist):
            guards.append(Expr('not', Expr('=', Expr(x), a)))
        return Expr(clause.op, list(map(Expr, funcproto.arglist))), guards
    a1, guard1 = _do_instrument_constraint(clause.arg1, funcproto)
    a2, guard2 = _do_instrument_constraint(clause.arg2, funcproto)
    a3, guard3 = _do_instrument_constraint(clause.arg3, funcproto)
    return Expr(clause.op, a1, a2, a3), guard1 + guard2 + guard3


def _assembly_clauses_with(op, clauses):
    if len(clauses) == 0:
        if op == 'or':
            return Expr(True)
        elif op == 'and':
            return Expr(False)
        else:
            assert False
    if len(clauses) == 1:
        return clauses[0]
    return Expr(op, _assembly_clauses_with(op, clauses[1:]), clauses[0])


def _assembly_constraint(clauses, guards):
    # guard = _assembly_clauses_with('and', guards)
    # clause = _assembly_clauses_with('or', clauses)
    # return Expr('', guard, clause)
    return _assembly_clauses_with('or', guards + clauses)


def _instrument_find_eqrewrite(guards):
    m = {}
    for g in guards:
        if g.op == 'not':
            t = g.arg1
            if t.op == '=':
                a1 = t.arg1
                a2 = t.arg2
                if not (isinstance(a1.op, str) and a1.arg1 is None):
                    continue
                if not (isinstance(a2.op, str) and a2.arg1 is None):
                    continue
                if not (a1.op.endswith('__Int') or a1.op.endswith('__Bool')):
                    if a1.op not in m:
                        m[a1.op] = {}
                    if a2.op not in m[a1.op]:
                        m[a1.op][a2.op] = 0
                    m[a1.op][a2.op] += 1
    return m


def _instrument_constraint(constraint, funcproto):
    clauses, guards = _instrument_split_constraint(constraint)
    newclauses = []
    newguards = []
    for c in clauses:
        newclause, newguardlist = _do_instrument_constraint(c, funcproto)
        newclauses.append(newclause)
        newguards.extend(newguardlist)
    m = _instrument_find_eqrewrite(newguards)
    return _assembly_constraint(newclauses, guards + newguards), m


def _get_instrumented_varmap(constraint, funcproto):
    if constraint is None:
        return {}
    if isinstance(constraint.op, int):
        return {}
    if isinstance(constraint.op, bool):
        return {}
    ret = {}
    if isinstance(constraint.op, Func):
        for l in constraint.arg1:
            m = _get_instrumented_varmap(l, funcproto)
            for t in m:
                ret[t] = m[t]
        return ret
    if constraint.op not in ['+', '-', '*', 'div', 'mod', 'ite', 'and', 'or',
                             '=>', 'xor', 'xnor', 'nand', 'nor', 'iff', 'not',
                             '=', '>=', '>', '<=', '<']:
        if constraint.op.endswith('Int'):
            return {constraint.op: 'Int'}
        elif constraint.op.endswith('Bool'):
            return {constraint.op: 'Bool'}
        else:
            return {constraint.op: funcproto.getargtype(constraint.op)}
    for arg in [constraint.arg1, constraint.arg2, constraint.arg3]:
        m = _get_instrumented_varmap(arg, funcproto)
        for t in m:
            ret[t] = m[t]
    return ret


def _get_instrumented_varlist(constraint, funcproto):
    varmap = _get_instrumented_varmap(constraint, funcproto)
    inputlist = []
    inputtylist = []
    for k in varmap:
        inputlist.append(k)
        inputtylist.append(varmap[k])
    return inputlist, inputtylist, varmap


def _findoverallmap(eqmaplist):
    eqmap = {}
    for m in eqmaplist:
        for k in m:
            for l in m[k]:
                if k not in eqmap:
                    eqmap[k] = {}
                if l not in eqmap[k]:
                    eqmap[k][l] = 0
                eqmap[k][l] += 1
    used = set()
    ret = {}
    for left in eqmap:
        m = eqmap[left]
        n = None
        max = 0
        for right in m:
            if right in used:
                continue
            if m[right] > max:
                max = m[right]
                n = right
        if n is not None:
            used.add(n)
            ret[left] = n
    return ret


def _subst_eqclass(expr, overallmap):
    if expr is None:
        return None
    op = expr.op
    if isinstance(op, int):
        return expr
    if isinstance(op, bool):
        return expr
    if isinstance(op, Func):
        return Expr(op, list(map(lambda x: _subst_eqclass(x, overallmap), expr.arg1)))
    if expr.arg1 is None:
        if expr.op in overallmap:
            return Expr(overallmap[expr.op])
        return expr
    return Expr(op,
                _subst_eqclass(expr.arg1, overallmap),
                _subst_eqclass(expr.arg2, overallmap),
                _subst_eqclass(expr.arg3, overallmap))


def _cleanup_eq(expr):
    if expr is None:
        return None
    op = expr.op
    if isinstance(op, int):
        return expr
    if isinstance(op, bool):
        return expr
    if isinstance(op, Func):
        return Expr(op, list(map(_cleanup_eq, expr.arg1)))
    if op == '=':
        if expr.arg1.arg1 is None and expr.arg1.op == expr.arg2.op:
            return Expr(True)
    if expr.arg1 is None:
        return expr
    arg1 = _cleanup_eq(expr.arg1)
    arg2 = _cleanup_eq(expr.arg2)
    arg3 = _cleanup_eq(expr.arg3)
    if op == 'not':
        if isinstance(arg1.op, bool):
            return Expr(not arg1.op)
    elif op == 'or':
        if isinstance(arg1.op, bool):
            if arg1.op:
                return Expr(True)
            else:
                return arg2
        if isinstance(arg2.op, bool):
            if arg2.op:
                return Expr(True)
            else:
                return arg1
    elif op == 'and':
        if isinstance(arg1.op, bool):
            if arg1.op:
                return arg2
            else:
                return Expr(False)
        if isinstance(arg2.op, bool):
            if arg2.op:
                return arg1
            else:
                return Expr(False)
    elif op == '=>':
        if isinstance(arg1.op, bool):
            if arg1.op:
                return arg2
            else:
                return Expr(True)
        if isinstance(arg2.op, bool):
            if arg2.op:
                return Expr(True)
            else:
                return arg1
    elif op == 'xor':
        if isinstance(arg1.op, bool):
            if arg1.op:
                if isinstance(arg2.op, bool):
                    return Expr(not arg2.op)
                else:
                    return Expr('not', arg2)
            else:
                return arg2
        if isinstance(arg2.op, bool):
            if arg2.op:
                return Expr('not', arg1)
            else:
                return arg1
    elif op in ['iff', '=', 'xnor']:
        if isinstance(arg1.op, bool):
            if arg1.op:
                return arg2
            else:
                if isinstance(arg2.op, bool):
                    return Expr(not arg2.op)
                else:
                    return Expr('not', arg2)
        if isinstance(arg2.op, bool):
            if arg2.op:
                return arg1
            else:
                return Expr('not', arg1)
    elif op == 'nand':
        if isinstance(arg1.op, bool):
            if arg1.op:
                if isinstance(arg2.op, bool):
                    return Expr(not arg2.op)
                else:
                    return Expr('not', arg2)
            else:
                return Expr(True)
        if isinstance(arg2.op, bool):
            if arg2.op:
                return Expr('not', arg1)
            else:
                return Expr(True)
    elif op == 'nor':
        if isinstance(arg1.op, bool):
            if arg1.op:
                return Expr(False)
            else:
                if isinstance(arg2.op, bool):
                    return Expr(not arg2.op)
                else:
                    return Expr('not', arg2)
        if isinstance(arg2.op, bool):
            if arg2.op:
                return Expr(False)
            else:
                return Expr('not', arg1)
    return Expr(op, arg1, arg2, arg3)


def _merge_eqclass(constraintlist, eqmaplist):
    overallmap = _findoverallmap(eqmaplist)
    inversemap = {}
    for o in overallmap:
        inversemap[overallmap[o]] = o
    return list(map(_cleanup_eq,
                    map(lambda x: _subst_eqclass(x, inversemap),
                        constraintlist)))


def _accumulate_call_params(constraint: Expr):
    if constraint is None:
        return None
    ret = []
    if isinstance(constraint.op, int):
        return None
    if isinstance(constraint.op, bool):
        return None
    if isinstance(constraint.op, Func):
        for t in constraint.arg1:
            ret.append({str(t)})
        for t in map(_accumulate_call_params, constraint.arg1):
            if t is not None:
                for i in range(len(ret)):
                    ret[i] = ret[i].union(t[i])
        return ret
    a1 = _accumulate_call_params(constraint.arg1)
    a2 = _accumulate_call_params(constraint.arg2)
    a3 = _accumulate_call_params(constraint.arg3)
    for t in [a1, a2, a3]:
        if t is not None:
            if len(ret) == 0:
                ret = t
            else:
                for i in range(len(ret)):
                    ret[i] = ret[i].union(t[i])
    if len(ret) == 0:
        return None
    else:
        return ret


def _check_single_call(constraint: Expr):
    r = _accumulate_call_params(constraint)
    for t in r:
        if len(t) > 1:
            return False
    return True

class TaskData:
    def __init__(self):
        self.bmExpr = None
        self.bmLogic = None
        self.bmSyn = None
        self.bmConstraint = None
        self.bmDefineFun = None
        self.bmDeclvar = None
        self.bmEnd = ['check-synth']
        self.constraint = None
        self.constraintlist = None
        self.inputlist = None
        self.inputtylist = None
        self.inputmap = None
        self.semchecker = None
        self.vartab = None
        self.z3checker = None


class SynthTask:
    def _stripComments(self, bmFile):
        noComments = '('
        for line in bmFile:
            line = line.split(';', 1)[0]
            noComments += line
        return noComments + ')'

    def __init__(self, filename, instrument=True):
        '''
        :param filename:
        There should be only one instance active
        '''
        benchmarkFile = open(filename)
        bm = self._stripComments(benchmarkFile)
        self.ori = TaskData()
        self.ins = None
        self.ori.bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
        self.ori.bmLogic = None
        self.ori.bmSyn = None
        self.ori.bmDeclvar = []
        self.ori.bmConstraint = []
        self.ori.bmDefineFun = []
        for expr in self.ori.bmExpr:
            if len(expr) == 0:
                continue
            elif expr[0] == 'set-logic':
                self.ori.bmLogic = expr
            elif expr[0] == 'synth-fun':
                self.ori.bmSyn = expr
            elif expr[0] == 'declare-var':
                self.ori.bmDeclvar.append(expr)
            elif expr[0] == 'constraint':
                self.ori.bmConstraint.append(expr)
            elif expr[0] == 'define-fun':
                self.ori.bmDefineFun.append(expr)
        # TODO: defining a function
        assert len(self.ori.bmDefineFun) == 0

        self._initialize_production()
        Expr.productions = self.productions
        self.ori.z3checker = translator.ReadQuery(self.ori.bmExpr)
        self.ori.inputlist, self.ori.inputtylist, self.ori.inputmap = _get_inputlists(self.ori.bmDeclvar)
        self.ori.constraintlist = _get_constraintlist(self.ori.bmConstraint, self.functionProto)
        self.ori.constraint = _constraintlist2conjunction(self.ori.constraintlist)
        self.ori.vartab = _getvartab(self.ori.inputlist, self.ori.inputtylist)

        self.ori.semchecker = SemChecker(
            self.functionProto,
            self.ori.constraint,
            self.ori.inputlist,
            self.ori.inputtylist)
        if instrument:
            self.ins = TaskData()
            self.ins.bmDefineFun = self.ori.bmDefineFun
            self.ins.bmLogic = self.ori.bmLogic
            self.ins.bmSyn = self.ori.bmSyn
            self._initialize_instrument()

    def _initialize_production(self):
        StartSym = 'My-Start-Symbol'
        StartBoolSym = 'My-Bool-Start-Symbol'
        SynFunExpr = self.ori.bmSyn

        productions = {StartSym: [], StartBoolSym: []}
        Type = {StartSym: SynFunExpr[3], StartBoolSym: 'Bool'}

        for NonTerm in SynFunExpr[4]:  # SynFunExpr[4] is the production rules
            NTName = NonTerm[0]
            NTType = NonTerm[1]
            if NTType == Type[StartSym]:
                productions[StartSym].append(NTName)
            if NTType == Type[StartBoolSym]:
                productions[StartBoolSym].append(NTName)
            Type[NTName] = NTType
            # Productions[NTName] = NonTerm[2]
            productions[NTName] = []
            for NT in NonTerm[2]:
                if type(NT) == tuple:
                    productions[NTName].append([NT[0], NT[
                        1]])  # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
                else:
                    productions[NTName].append(NT)
        # eliminateProductions(productions)

        arglist = []
        typelist = []
        for p in SynFunExpr[2]:
            arglist.append(p[0])
            typelist.append(p[1])
        functionProto = Func(SynFunExpr[1], arglist, typelist, SynFunExpr[3])
        self.productions = productions
        self.functionProto = functionProto

    def _initialize_instrument(self):
        cnf = buildCNF(self.ori.constraint, self.ori.vartab, self.functionProto)
        cnfsuffix = _instrument_add_suffix(cnf, self.ori.inputmap)
        cnfconstrains = getCNFclause(cnfsuffix)
        if not all(map(_check_single_call, cnfconstrains)):
            self.ins = self.ori
            return
        constraintlist, eqmaplist = zip(
            *list(map(lambda x: _instrument_constraint(x, self.functionProto), cnfconstrains)))
        self.ins.constraintlist = _merge_eqclass(constraintlist, eqmaplist)
        self.ins.constraint = _assembly_clauses_with('and', self.ins.constraintlist)
        self.ins.inputlist, self.ins.inputtylist, self.ins.inputmap = \
            _get_instrumented_varlist(self.ins.constraint, self.functionProto)
        self.ins.bmDeclvar = []
        for m in self.ins.inputmap:
            self.ins.bmDeclvar.append(['declare-var', m, self.ins.inputmap[m]])
        self.ins.bmConstraint = []
        for c in self.ins.constraintlist:
            self.ins.bmConstraint.append(['constraint', exprToList(c)])
        self.ins.bmExpr = \
            [self.ins.bmLogic] + \
            self.ins.bmDeclvar + \
            self.ins.bmDefineFun + \
            [self.ins.bmSyn] + \
            self.ins.bmConstraint + \
            [self.ins.bmEnd]
        self.ins.z3checker = translator.ReadQuery(self.ins.bmExpr)
        self.ins.vartab = _getvartab(self.ins.inputlist, self.ins.inputtylist)
        self.ins.semchecker = SemChecker(
            self.functionProto,
            self.ins.constraint,
            self.ins.inputlist,
            self.ins.inputtylist)
        i = 1
