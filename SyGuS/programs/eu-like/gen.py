import random
import translator
import pprint

def varName(k):
    return "x" + str(k)


if __name__ == '__main__':
    n = 5
    N = 2 ** n
    m = N - 1
    value = [i for i in range(N)]
    random.shuffle(value)

    data = []
    A = []
    for i in range(n):
        A.append([">=", varName(i), str(0)])
        A.append(["<", varName(i), str(N)])
    Left = A[0]
    for a in A[1:]:
        Left = ["and", a, Left]

    functionCall = ["f"]
    for i in range(n):
        functionCall.append(varName(i))

    A = []
    for i in range(n):
        step = 2 ** (i + 1)
        leftCons = ["<=", varName(i), str(random.randint(0, N-1))]
        B = []
        start = 0
        while start < N:
            for i in range(step // 2):
                B.append(["=", functionCall, str(value[start + i])])
            start += step
        rightCons = B[0]
        for a in B[1:]:
            rightCons = ["or", a, rightCons]
        A.append(["iff", leftCons, rightCons])
    A.append(["and", [">=", functionCall, str(0)], ["<=", functionCall, str(m)]])

    Right = A[0]
    for a in A[1:]:
        Right = ["and", a, Right]

    Cons = ["constraint", ["=>", Left, Right]]
    pprint.pprint(Cons)
    print(translator.toString(Cons))
