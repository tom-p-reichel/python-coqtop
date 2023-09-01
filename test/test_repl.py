from coqtop.repl import REPL
from coqtop.xsync import xroutine
import time
import asyncio as aio
from unittest import IsolatedAsyncioTestCase

@xroutine
def test(r):
    n = 10000
    for i in range(n):
        out = yield from r.call(f"Definition v{i} := True.\n")
        assert(out[0]==f"v{i} is defined\n".encode())

@xroutine
def test2(r):
    n = 100000
    futures = [r.call(f"Definition v{x} := True.\n") for x in range(n)]
    for i,x in zip(range(n),futures):
        out = yield from x
        assert(out[0]==f"v{i} is defined\n".encode())

@xroutine
def test3(r):
    n = 100000
    out = yield from r.call("".join([f"Definition v{x} := True.\n" for x in range(100000)]))
    assert(out[0]=="".join([f"v{i} is defined\n" for i in range(n)]).encode())


class TestRepl(IsolatedAsyncioTestCase):

    async def tester(self):

        for t in [test,test2,test3]:
            stamp = time.time()
            r = REPL("coqtop")
            t(r).block()
            r = REPL("coqtop")
            r.make_async()
            await t(r)
            print(time.time()-stamp)

