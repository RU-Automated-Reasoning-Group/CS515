import sys

from possibleterm.possibleterm import findPossibleValue
from semantics.semantics import exprFromList
from instrument.task import SynthTask
from decisiontree.treelearning import TreeLearner, genmoreconstraint


def main():
    task = SynthTask(sys.argv[1])
    if task.ins is task.ori:
        exit(0)
    possiblevalue = list(map(lambda l: exprFromList(l, [task.functionProto]),
                             findPossibleValue(task.ins.bmExpr)))
    moreconstraint = genmoreconstraint(task.productions, task.ins.inputlist, task.ins.inputtylist)
    treelearner = TreeLearner(task.ins.semchecker, task.ins.z3checker, possiblevalue, moreconstraint)
    expr = treelearner.mainalgo()
    task.functionProto.expr = expr
    print(task.functionProto)
    #print(treelearner.mainalgo())
    #expr = Expr('ite', Expr('>=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))
    #expr = Expr('ite', Expr('<=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))



if __name__ == '__main__':
    main()


