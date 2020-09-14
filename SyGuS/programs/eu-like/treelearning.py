import math

import z3.z3

from enumerate import enumerateBool, resetHeap
from semantics import Expr
from treedef import TreeLeaf, TreeInnerNode


class TreeLearner:
    def __init__(self, semchecker, z3checker):
        self.funcproto = semchecker.funcproto
        self.inputlist = semchecker.inputlist
        self.inputtylist = semchecker.inputtylist
        self.semchecker = semchecker
        self.z3checker = z3checker
        self.pts = []
        self.ptsinner = []
        self.terms = []
        self.preds = []
        self.covers = []
        self.labels = []
        self.partitions = []
        self.pickedpred = []
        self.lastterms = []

    def gencover(self, pts, term):
        cover = set()
        idx = 0
        for pt in pts:
            symtab = pt
            if self.semchecker.check(term, symtab):
                # TODO: may improve performance here
                cover.add(idx)
            idx += 1
        return cover

    def nextDistinctTerm(self, pts):
        '''
        p = [Expr('x1'),
             Expr('x2'),
             Expr('x3'),
             Expr('x4'),
             Expr('x5'),
             Expr('x6')]
        p = [Expr('x'),
             Expr('y'),
             Expr('z'),
             Expr('u'),
             Expr('w')]
        p = []
        for i in range(8):
            p.append(Expr(i))
        '''
        # p = [Expr(-1),Expr(1),Expr('+', Expr('x'), Expr('y'))]
        p = [Expr(0), Expr(10), Expr(20), Expr(30), Expr(40), Expr(50), Expr('x')]

        if len(self.terms) < len(p):
            t = p[len(self.terms)]
            ct = self.gencover(pts, t)
            # if self.covers.count(ct) == 0:
            for i in ct:
                self.labels[i].add(len(self.terms))
            self.terms.append(t)
            self.covers.append(ct)
        return
        '''
        while True:
            t = enumerateTerm()
            ct = self.gencover(pts, t)
            if self.covers.count(ct) == 0:
                for i in ct:
                    self.labels[i].add(len(self.terms))
                self.terms.append(t)
                self.covers.append(ct)
                return
        '''

    def genpartition(self, pred):
        partition = (set(), set())
        idx = 0
        for pt in self.ptsinner:
            symtab = pt
            self.funcproto.expr = pred
            if pred.eval(symtab):
                partition[0].add(idx)
            else:
                partition[1].add(idx)
            idx += 1
        return partition

    def nextPred(self):
        pred = enumerateBool()
        if pred == None:
            return
        partition = self.genpartition(pred)
        self.preds.append(pred)
        self.partitions.append(partition)
        self.pickedpred.append(False)

    def conditionalProb(self, ptsprime, ptidx, labelidx):
        if ptidx not in self.covers[labelidx]:
            return 0
        coverset = self.covers[labelidx].intersection(ptsprime)
        tot = 0
        for t in self.labels[ptidx]:
            tot += len(self.covers[t].intersection(ptsprime))
        num = len(coverset.intersection(ptsprime))
        return num / tot

    def unconditionalProb(self, ptsprime, labelidx):
        all = 0
        for i in ptsprime:
            all += self.conditionalProb(ptsprime, i, labelidx)
        return all / len(ptsprime)

    def entropy(self, ptsset, ptsprime):
        tot = 0
        for t in range(len(self.terms)):
            prob = self.unconditionalProb(ptsprime, t) + 0.00000001
            tot -= prob * math.log2(prob)
        return tot

    def gain(self, partition, ptsset):
        tot = 0
        l = len(partition[0].intersection(ptsset))
        if l == 0 or l == len(ptsset):
            return 1000000
        for i in range(2):
            # print(ptsset, partition[i])

            tot += len(partition[i].intersection(ptsset)) / len(ptsset) * self.entropy(ptsset, partition[i].intersection(ptsset))
        return tot

    def pickPred(self, ptsset):
        maxgain = 10000
        picked = -1
        # print('in')
        # print(ptsset)
        for p in range(len(self.preds)):
            if self.pickedpred[p]:
                continue
            g = self.gain(self.partitions[p], ptsset)
            # print(len(self.partitions[p][0].intersection(ptsset)), len(self.partitions[p][1].intersection(ptsset)), g)
            if g < maxgain:
                picked = p
                maxgain = g
        return picked

    depth = 0

    def learntree(self, ptsset):
        # print(self.depth, ptsset)
        self.depth += 1
        for i in range(len(self.covers)):
            if ptsset.issubset(self.covers[i]):
                self.depth -= 1
                return TreeLeaf(self.terms[i])
        if len(self.preds) == 0:
            self.depth -= 1
            return None
        picked = self.pickPred(ptsset)
        if picked == -1:
            self.depth -= 1
            return None
        self.pickedpred[picked] = True
        l = self.learntree(self.partitions[picked][0].intersection(ptsset))
        if l is None:
            self.depth -= 1
            self.pickedpred[picked] = False
            return None
        r = self.learntree(self.partitions[picked][1].intersection(ptsset))
        self.pickedpred[picked] = False
        if r is None:
            self.depth -= 1
            return None
        self.depth -= 1
        return TreeInnerNode(self.preds[picked], l, r)

    def verifyExpr(self, expr):
        randomConstraint = [
            ['constraint', ['>=', 'x', '5']],
            ['constraint', ['>=', 'y', '5']],
            ['constraint', ['>=', 'z', '5']],
            ['constraint', ['>=', 'w', '5']],
            ['constraint', ['true']]
        ]
        self.funcproto.expr = expr

        counterexample = self.z3checker.check(str(self.funcproto), [])
        if counterexample is None:
            return None, None
        # counterexample = self.z3checker.check(str(self.funcproto), randomConstraint)
        symtab = {}
        for i in range(len(self.inputlist)):
            s = self.inputlist[i]
            if self.inputtylist[i] == 'Int':
                symtab[s] = int(str(counterexample.eval(z3.Int(s), True)))
            else:
                symtab[s] = int(str(counterexample.eval(z3.Bool(s), True)))
        innersymtab = self.semchecker.getSymtab(symtab)
        symtab = [symtab] * len(innersymtab)
        return innersymtab, symtab

    def mainalgo(self):
        self.pts = []
        i = 0
        while True:
            self.terms = []
            self.preds = []
            self.covers = []
            self.labels = []
            self.partitions = []
            self.pickedpred = []
            resetHeap()

            for i in range(len(self.pts)):
                self.labels.append(set())
            tree = None
            allunion = set()
            while len(allunion) != len(self.pts):
                self.nextDistinctTerm(self.pts)
                allunion = allunion.union(self.covers[-1])
            tree = self.learntree(set(range(len(self.pts))))
            while tree is None:
                self.nextDistinctTerm(self.pts)
                self.nextPred()
                tree = self.learntree(set(range(len(self.pts))))
            e = tree.getExpr()
            i = i + 1
            print(e)
            innersymtabs, symtabs = self.verifyExpr(e)
            if innersymtabs is None:  # len(cexample) == None:
                print('iter:', i)
                print('size:', e.size)
                return e
            self.pts.extend(symtabs)
            self.ptsinner.extend(innersymtabs)
            # self.pts.extend(cexample)







