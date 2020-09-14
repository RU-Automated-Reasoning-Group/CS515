import heapq

from semantics.semantics import Expr

heap = []
used = set()
boolheap = []
boolused = set()


def resetHeap():
    global heap, used, boolheap, boolused
    heap.clear()
    used.clear()
    boolheap.clear()
    boolused.clear()
    heapq.heappush(heap, Expr('My-Start-Symbol'))
    heapq.heappush(boolheap, Expr('My-Bool-Start-Symbol'))


def enumerate(heap, used):
    while True:
        if len(heap) == 0:
            return None
        p = heapq.heappop(heap)
        ex = p.extend()
        for t in ex:
            if str(t) in used:
                continue
            used.add(str(t))
            heapq.heappush(heap, t)
        if p.hole == 0:
            return p

def enumerateTerm():
    global heap, used
    return enumerate(heap, used)


def enumerateBool():
    global boolheap, boolused
    return enumerate(boolheap, boolused)

def registerTerm(term):
    used.add(str(term))