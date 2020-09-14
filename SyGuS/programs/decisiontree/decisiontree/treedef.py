from semantics.semantics import Expr


class TreeNode:
    pass


class TreeLeaf(TreeNode):
    def __init__(self, term):
        self.term = term
    def getExpr(self):
        return self.term


class TreeInnerNode(TreeNode):
    def __init__(self, pred, left, right):
        self.pred = pred
        self.left = left
        self.right = right
    def getExpr(self):
        return Expr('ite', self.pred, self.left.getExpr(), self.right.getExpr())