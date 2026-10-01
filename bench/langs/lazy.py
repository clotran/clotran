import time, itertools
class Cell:  # a memoized thunk cell per element, as a Clojure lazy-seq is
    __slots__ = ("head", "thunk", "val", "done")
    def __init__(s, h, t): s.head, s.thunk, s.done = h, t, False
    def tail(s):
        if not s.done: s.val, s.done, s.thunk = s.thunk(), True, None
        return s.val
def frm(n): return Cell(n, lambda: frm(n + 1))
def take_s(n, s): return None if n == 0 or s is None else Cell(s.head, lambda: take_s(n - 1, s.tail()))
def sum_s(s):
    a = 0
    while s is not None: a += s.head; s = s.tail()
    return a
def rng():
    i = 0
    while True: yield i; i += 1
def take(n, it):
    for x in it:
        if n <= 0: return
        yield x; n -= 1
for label, f in [("sum(islice(count(), n))  (C iterators)", lambda: sum(itertools.islice(itertools.count(), 1000000))),
                 ("sum(take(n, rng()))  (generators)", lambda: sum(take(1000000, rng()))),
                 ("sum_s(take_s(n, frm(0)))  (hand stream)", lambda: sum_s(take_s(1000000, frm(0))))]:
    f(); t = time.perf_counter(); r = f(); print(f"{label:44s} {1000*(time.perf_counter()-t):8.1f} ms  ({r})")
