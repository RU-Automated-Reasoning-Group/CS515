import abc
import re
import sys
from collections import defaultdict
from itertools import product


class Dag(object):
    def __init__(self, n, n1, n2, edges=None, w=None):
        self.n = n
        self.source = n1
        self.dest = n2
        self.edges = edges
        self.w = w

    def __str__(self):
        return str(self.w)

    def __repr__(self):
        return self.__str__()

    def get_path(self):
        # type: () -> list
        ret = []
        for edge in self.edges:
            if not any(edge.a):
                path = [edge]
                res = self.__get_path(path)
                if res:
                    ret.append(path)
        return ret

    def generate(self, original_str):
        paths = self.get_path()
        result_dict = defaultdict(int)
        if len(paths) > 0:
            for path in paths:
                # edges = [next(iter(self.w[k])) for k in path]
                potential_edge_lists = product(*[self.w[k] for k in path])
                for edge_list in potential_edge_lists:
                    res = apply_path(edge_list, original_str)
                    if res is not None:
                        for k, v in res.items():
                            result_dict[k] += v
        return result_dict

    def __get_path(self, path):
        last_edge = path[-1]
        if last_edge.b == self.dest:
            return True
        for edge in self.edges:
            if edge.a == last_edge.b:
                path.append(edge)
                if self.__get_path(path):
                    return True
                path.pop(-1)
        return False

    def get_simples(self):
        list1 = []



class Edge(object):
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def __hash__(self):
        return 31 * hash(self.a) + hash(self.b)

    def __eq__(self, other):
        return self.a == other.a and self.b == other.b

    def __cmp__(self, other):
        if self.a == other.a and self.b == other.b:
            return 0
        if self.a < other.a or (self.a == self.a and self.b < other.b):
            return -1
        return 1

    def __repr__(self):
        return "<Edge: " + str(self.a) + ", " + str(self.b) + ">"

    def __str__(self):
        return self.__repr__()


class Token(object):
    __metaclass__ = abc.ABCMeta

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return isinstance(other, self.__class__)

    @abc.abstractmethod
    def reg_str(self):
        return


class StartToken(Token):
    def __init__(self):
        super(StartToken, self).__init__()

    def __repr__(self):
        return "StartToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r"^"


class EndToken(Token):
    def __init__(self):
        super(EndToken, self).__init__()

    def __repr__(self):
        return "EndToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r"$"


class NullToken(Token):
    def __init__(self):
        super(NullToken, self).__init__()

    def __repr__(self):
        return "NullToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r""


class AlphaToken(Token):
    def __init__(self):
        super(AlphaToken, self).__init__()

    def __repr__(self):
        return "AlphaToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r"(?<![A-Za-z])[A-Za-z]+(?![A-Za-z])"


class NumToken(Token):
    def __init__(self):
        super(NumToken, self).__init__()

    def __repr__(self):
        return "NumToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r"(?<!\d)\d+(?!\d)"


class SpaceToken(Token):
    def __init__(self):
        super(SpaceToken, self).__init__()

    def __repr__(self):
        return "SpaceToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r"(?<! ) +(?! )"


class UpperToken(Token):
    def __init__(self):
        super(UpperToken, self).__init__()

    def __repr__(self):
        return "UpperToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r"(?<![A-Z])[A-Z]+(?![A-Z])"


class LowerToken(Token):
    def __init__(self):
        super(LowerToken, self).__init__()

    def __repr__(self):
        return "LowerToken"

    def __str__(self):
        return self.__repr__()

    def reg_str(self):
        return r"(?<![a-z])[a-z]+(?![a-z])"


class Node(object):
    def __init__(self):
        pass


class Expression(object):
    def __init__(self):
        pass


class Substr(Expression):
    def __init__(self, p1: set, p2: set) -> None:
        super(Substr, self).__init__()
        self.vi = 0
        self.p1 = p1
        self.p2 = p2

    def __repr__(self):
        return "<Substr: " + str(self.p1) + ", " + str(self.p2) + ">"

    def __str__(self):
        return self.__repr__()

    def get_simples(self):
        return [Substr({item1}, {item2}) for item1 in self.p1 for item2 in self.p2]


class ConstStr(Expression):
    def __init__(self, s):
        super(ConstStr, self).__init__()
        self.s = s

    def __eq__(self, other):
        return self.s == other.s

    def __hash__(self):
        return hash(self.s)

    def __cmp__(self, other):
        return self.s.__cmp__(other.s)

    def __repr__(self):
        return "<ConstStr: " + str(self.s) + ">"

    def __str__(self):
        return self.__repr__()

    def get_simples(self):
        return [self]


class Loop(Expression):
    def __init__(self, dag: Dag):
        super(Loop, self).__init__()
        self.dag = dag

    def __eq__(self, other):
        return self.dag == other.dag

    def __hash__(self):
        return hash(self.dag)

    def __repr__(self):
        return "<Loop: " + str(self.dag) + ">"

    def __str__(self):
        return self.__repr__()


class CPos(object):
    def __init__(self, pos, delta=0):
        self.pos = pos
        self.delta = delta

    def __eq__(self, other):
        return self.pos == other.pos and self.delta == self.delta

    def __hash__(self) -> int:
        return hash(self.pos) * 31 + hash(self.delta)

    def __cmp__(self, other):
        return self.pos.__cmp__(other.pos)

    def __repr__(self):
        return "<CPos: " + str(self.pos) + (", " + str(self.delta) if self.delta != 0 else "") + ">"

    def __str__(self):
        return self.__repr__()

    def match(self, s):
        if -len(s) - 1 <= self.pos < 0:
            return {len(s) + self.pos + 1}
        elif 0 <= self.pos < len(s):
            return {self.pos}
        return None


class Pos(object):
    def __init__(self, reg_list1, reg_list2, c=set()):
        self.reg_list1, self.reg_list2 = reg_list1, reg_list2
        self.c = c

    def __repr__(self):
        return "<Pos: " + str(self.reg_list1) + str(self.reg_list2) + str(self.c) + ">"

    def __str__(self):
        return self.__repr__()

    def match(self, string):
        tokens1 = tuple((item[0] for item in self.reg_list1))
        tokens2 = tuple((item[0] for item in self.reg_list2))

        matches = []
        for i in range(len(string) + 1):
            if match_start(string, i, tokens2)[0] and match_end(string, i, tokens1)[0]:
                matches.append(i)

        if len(matches) == 0:
            return None

        res = set((matches[i] for i in self.c if -len(matches) <= i < len(matches)))
        if len(res) == 0:
            return None

        return res


def intersect_pos(pos_set1, pos_set2, is_unity=False):
    res = set()

    for op1 in pos_set1:
        for op2 in pos_set2:
            if isinstance(op1, CPos) and isinstance(op2, CPos):
                if op1 == op2:
                    res.add(CPos(op1.pos))
                if op1 != op2 and is_unity and 0 <= op1.pos < op2.pos or op2.pos < op1.pos < 0:
                    res.add(CPos(op1.pos, op2.pos - op1.pos))
            elif isinstance(op1, Pos) and isinstance(op2, Pos):
                rl1 = intersect_regex(op1.reg_list1, op2.reg_list1)
                rl2 = intersect_regex(op1.reg_list2, op2.reg_list2)
                if is_unity:
                    c = set([CPos(p1, p2 - p1) for p1 in op1.c for p2 in op2.c if 0 <= p1 < p2 or p2 < p1 < 0])
                else:
                    c = op1.c.intersection(op2.c)
                if rl1 is not None and rl2 is not None and len(c) > 0:
                    res.add(Pos(rl1,
                                rl2,
                                c))

    return res


def intersect_regex(rl1, rl2):
    res = None

    if len(rl1) == len(rl2):
        res = [tuple(set(rl1[i]) & set(rl2[i])) for i in range(len(rl1))]

        for item in res:
            if len(item) == 0:
                return None

    return res


def intersect(op1, op2, is_unity=False):
    res = None

    if isinstance(op1, Dag) and isinstance(op2, Dag):
        res = Dag(list(product(op1.n, op2.n)), op1.source + op2.source, op1.dest + op2.dest)
        res.edges = list((Edge(edge1.a + edge2.a, edge1.b + edge2.b) for
                          edge1, edge2 in product(op1.edges, op2.edges)))
        res.w = {Edge(edge1.a + edge2.a, edge1.b + edge2.b): set(
            filter(lambda x: x is not None, (intersect(f1, f2, is_unity) for f1 in op1.w[edge1] for f2 in op2.w[edge2])))
            for edge1, edge2 in product(op1.edges, op2.edges)}
        res.w = {k: v for k, v in res.w.items() if len(v) > 0}
        res.edges = res.w.keys()

    elif isinstance(op1, Substr) and isinstance(op2, Substr):
        # this condition is useless -- all vi are equal now
        if op1.vi == op2.vi:
            p1 = intersect_pos(op1.p1, op2.p1, is_unity)
            p2 = intersect_pos(op1.p2, op2.p2, is_unity)
            if len(p1) > 0 and len(p2) > 0:
                res = Substr(p1, p2)
    elif isinstance(op1, ConstStr) and isinstance(op2, ConstStr):
        if op1 == op2:
            res = op1
    elif isinstance(op1, Loop) and isinstance(op2, Loop):
        res = Loop(intersect(op1.dag, op2.dag, is_unity))

    return res


def generate_str(sigma, s, need_loop=True):
    n = list(range(len(s) + 1))
    source = (0,)
    dest = (len(s),)
    edges = list((Edge((x[0],), (x[1],)) for x in filter(lambda x: x[0] < x[1], product(n, n))))
    W = {}
    for edge in edges:
        w = {ConstStr(s[edge.a[0]: edge.b[0]])}
        w = w.union(generate_substring(sigma, s[edge.a[0]: edge.b[0]]))
        W[edge] = w
    if need_loop:
        W = generate_loop(sigma, s, W)
    return Dag(n, source, dest, edges, W)


def intersect_list(l1, l2):
    # type: (list, list) -> list
    return list(set(l1) & set(l2))


def generate_partition(T):
    # type: (set) -> set
    res = None
    for item1 in T:
        for item2 in T:
            pass


# I don't plan to support multiple input string
def generate_loop(sigma, s, W):
    # type: (list(str), str, dict) -> dict

    original_str = sigma[0]
    for k1 in range(len(s)):
        for k2 in range(k1 + 1, len(s)):
            for k3 in range(k2 + 1, len(s) + 1):
                e1 = generate_str(sigma, s[k1:k2], False)
                e2 = generate_str(sigma, s[k2:k3], False)
                e = intersect(e1, e2, True)

                l = [Loop(e)]
                res_str_dict = apply_path(l, original_str)
                if '' in res_str_dict:
                    res_str_dict.pop('')
                for res_str in res_str_dict:
                    if s.startswith(res_str, k1):
                        W[Edge((k1,), (k1 + len(res_str),))].add(Loop(e))

    return W


def generate_substring(sigma, substr):
    # type: (list(str), str) -> set
    res = set()

    for string in sigma:
        begin = 0
        while True:
            begin = string.find(substr, begin)
            if begin == -1:
                break

            Y1 = generate_position(string, begin)
            Y2 = generate_position(string, begin + len(substr))

            begin += 1

            res.add(Substr(Y1, Y2))

    return res


def generate_position(s: str, k: int) -> set:
    res = {CPos(k), CPos(-(len(s) - k + 1))}

    reps = list(t[0] for t in calculate_iparts(s))

    n = 1
    rl1 = []
    rl2 = []
    pos1 = []
    pos2 = []
    while n <= 1:
        matched = False
        temp_rl = tuple(product(*((reps,) * n)))
        for r in temp_rl:
            match_res = match_end(s, k, r)
            if match_res[0]:
                matched = True
                rl1.append(r)
                pos1.append(match_res[1])

            match_res = match_start(s, k, r)
            if match_res[0]:
                matched = True
                rl2.append(r)
                pos2.append(match_res[2])

        n += 1

        if not matched:
            break

    for x, y in product(range(len(rl1)), range(len(rl2))):
        rl = rl1[x] + rl2[y]
        match_res = match(s, rl)

        for i, res_item in enumerate(match_res):
            if res_item[1] == pos1[x] and res_item[2] == pos2[y]:
                r1 = generate_regex(rl1[x], s)
                r2 = generate_regex(rl2[y], s)
                if len(r1) == 1 and len(r2) == 1:
                    if (NullToken() in r1[0] and NullToken() in r2[0]) or (StartToken() in r1[0] and StartToken() in r2[0])\
                            or (EndToken() in r1[0] and EndToken() in r2[0]):
                        continue
                # res.add(Pos(r1, r2, {i, -(len(match_res) - i + 1)}))
                res.add(Pos(r1, r2, {i, -(len(match_res) - i)}))

    return res


def generate_regex(r, s):
    global iparts

    res = []

    for token in r:
        for ipart in iparts[s]:
            if token in ipart:
                res.append(ipart)

    return res


def get_reg_str(token_list):
    reg_str = ""
    for item in token_list:
        reg_str += item.reg_str()

    return reg_str


def match(s, reg):
    reg_str = get_reg_str(reg)

    return list(((m.group(0), m.start(), m.end()) for m in re.finditer(reg_str, s)))


def match_start(s: str, i: int, token_list: tuple) -> list:
    pattern = get_reg_str(token_list)

    for m in re.finditer(pattern, s):
        if m.start() == i:
            res = [True, m.start(), m.end()]
            return res

    return [False]


def match_end(s: str, i: int, token_list: tuple) -> list:
    pattern = get_reg_str(token_list)

    for m in re.finditer(pattern, s):
        if m.end() == i:
            res = [True, m.start(), m.end()]
            return res

    return [False]


def calculate_iparts(s):
    return (NumToken(),), (AlphaToken(),), (StartToken(),), (EndToken(),), (SpaceToken(),), (UpperToken(),), (
        LowerToken(),), (NullToken(),)


def apply_path(operations, string):
    # type: (list, str) -> dict()
    res = defaultdict(int)
    res[''] = 0
    for op in operations:
        this_res = defaultdict(int)
        if isinstance(op, ConstStr):
            this_res[op.s] += 1
        elif isinstance(op, Substr):
            for p1 in op.p1:
                for p2 in op.p2:
                    ind_set1 = p1.match(string)
                    ind_set2 = p2.match(string)

                    if ind_set1 is None or ind_set2 is None:
                        this_res[''] += 1
                        continue

                    for ind1 in ind_set1:
                        for ind2 in ind_set2:
                            if ind1 < ind2:
                                this_res[string[ind1: ind2]] += 1

        elif isinstance(op, Loop):
            this_res[''] = 0
            dag = Dag(op.dag.n, op.dag.source, op.dag.dest, edges=op.dag.edges, w=dict())

            t = 0
            finished = False
            while not finished:
                for key in op.dag.w:
                    new_exp_set = set()
                    for exp in op.dag.w[key]:
                        if isinstance(exp, Substr):
                            new_p1 = set()

                            for new_pos in exp.p1:
                                if isinstance(new_pos, CPos):
                                    if new_pos.delta == 0:
                                        new_p1.add(new_pos)
                                    new_p1.add(CPos(new_pos.pos + t * new_pos.delta))
                                elif isinstance(new_pos, Pos):
                                    new_c = set([x.pos + t * x.delta for x in new_pos.c
                                                 if isinstance(x, CPos) and x.delta != 0]).union(
                                        set([x for x in new_pos.c if not isinstance(x, CPos)])
                                    )
                                    if len(new_c) > 0:
                                        new_p1.add(Pos(new_pos.reg_list1, new_pos.reg_list2,
                                                          new_c))

                            new_p2 = set()
                            for new_pos in exp.p2:
                                if isinstance(new_pos, CPos):
                                    if new_pos.delta == 0:
                                        continue
                                    new_p2.add(CPos(new_pos.pos + t * new_pos.delta))
                                elif isinstance(new_pos, Pos):
                                    new_c = set([x.pos + t * x.delta for x in new_pos.c
                                                 if isinstance(x, CPos) and x.delta != 0]).union(
                                        set([x for x in new_pos.c if not isinstance(x, CPos)])
                                    )
                                    if len(new_c) > 0:
                                        new_p2.add(Pos(new_pos.reg_list1, new_pos.reg_list2,
                                                          new_c))

                            if len(new_p1) == 0 or len(new_p2) == 0:
                                continue
                            new_exp = Substr(new_p1, new_p2)
                            new_exp_set.add(new_exp)
                    dag.w[key] = new_exp_set
                t += 1
                matched = dag.generate(string)

                if len(matched) > 0:
                    __this_res = defaultdict(int)
                    for k, v in this_res.items():
                        for k2, v2 in matched.items():
                            __this_res[k + k2] += v + v2

                    this_res = __this_res

                if len(matched) == 0 or (len(matched) == 1 and '' in matched):
                    finished = True

        __res = defaultdict(int)
        for k, v in res.items():
            for k2, v2 in this_res.items():
                __res[k + k2] += v + v2
        res = __res


    return res


if __name__ == "__main__":
    DEBUG = False

    i = 0
    iparts = dict()
    dag = None

    print("Please enter your data, e.g. World Wide Web,WWW (no space around the comma)")
    while True:
        l = input().strip()
        if l == '':
            break
        long_str, sub_str = l.split(",")
        iparts[long_str] = calculate_iparts(long_str)
        this_dag = generate_str((long_str,), sub_str)
        if dag is None:
            dag = this_dag
        else:
            dag = intersect(dag, this_dag)

        if DEBUG:
            print("ok")

    paths = dag.get_path()
    if len(paths) > 0:
        # path = min(paths, key=len)

        if DEBUG:
            paths = sorted(paths, key=len)
            for path in paths:
                edges = [next(iter(dag.w[k])) for k in path]
                print(edges)
        else:
            print("Please input new strings you want to manipulate")

        while True:
            long_str = sys.stdin.readline()
            result = dag.generate(long_str.strip())
            if result is not None:
                print(max(result, key=result.get))
            else:
                print("Can't handle it")

    else:
        print("Can't handle it")
