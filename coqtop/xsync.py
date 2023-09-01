import asyncio as aio

class xwrap():
    def __init__(self,gen):
        self.gen = gen

    def __iter__(self):
        return (yield from self.gen)

    def block(self):
        try:
            fut = next(self.gen)
            while True:
                out = fut.block()
                fut = self.gen.send(out)
        except StopIteration as e:
            return e.value

    def __await__(self):
        try:
            fut = next(self.gen)
            while True:
                out = yield from fut.__await__()
                fut = self.gen.send(out)
        except StopIteration as e:
            return e.value


def xroutine(f):
    def g(*args,**kwargs):
        return xwrap(f(*args,**kwargs))
    return g


class xfuture():
    def __iter__(self):
        return (yield self)


""" example

import time

class sleepfuture(xfuture):
    def __init__(self,msg):
        self.msg=msg

    def block(self):
        time.sleep(1)
        return self.msg

    def __await__(self):
        yield from aio.sleep(1).__await__()
        return self.msg

@xroutine
def f():
    a = yield from sleepfuture("first ")
    b = yield from sleepfuture("second")
    return a+b

@xroutine
def main():
    return (yield from f())

print(main().block())

async def main2():
    return await f()

print(aio.run(main2()))

"""
