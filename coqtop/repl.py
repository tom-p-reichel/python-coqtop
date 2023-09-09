import subprocess
import pathlib
import os
import queue
import collections
import ujson
import re
import select
import asyncio as aio
import sys
import tempfile
import ctypes as ct
import struct
from .xsync import xroutine, xfuture

preloaders = list(pathlib.Path(__file__).absolute().parent.glob("preloadtricks*so"))

assert len(preloaders)==1, "preloadtricks shared object missing. Did this library build correctly?"

preload = preloaders[0]

prngs = list(pathlib.Path(__file__).absolute().parent.glob("prng*so"))

assert len(prngs)==1, "prng shared object missing. Did this library build correctly?"

prng = ct.CDLL(prngs[0])


class PRNG():
    """ The exact same PRNG that the preloaded shim is using. """
    def __init__(self):
       self.state = (ct.c_char*prng.prng_struct_size())()
       prng.prng_init(self.state)
       self.next = prng.prng_pull(self.state)
    def __call__(self):
        tmp = self.next
        self.next = prng.prng_pull(self.state)
        return tmp
    def peek(self):
        return self.next
    def reset(self):
        prng.prng_init(self.state)
 

class REPL():
     class Request(xfuture):
        def __init__(self,repl,future=None):
            self.repl = repl
            self.future = future

        def block(self):
            if (hasattr(self,"result")):
                return self.result
            self.repl.block_for(self)
            return self.result
        
        def __await__(self):
            if (hasattr(self,"result")):
                return self.result
            self.result = yield from self.future.__await__()
            return self.result

     def __init__(self,command,*args,verbose=False):
        self.verbose=verbose
        self.is_async=False
        self.prng = PRNG()
        new_env = os.environ.copy()
        new_env["LD_PRELOAD"] = preload
        self.proc = subprocess.Popen([command]+list(args),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,env=new_env)
        os.set_blocking(self.proc.stdin.fileno(),False)
        os.set_blocking(self.proc.stdout.fileno(),False)
        os.set_blocking(self.proc.stderr.fileno(),False)
        # chunks of text read from stdout
        self.stdoutq = bytearray()
        # chunks of text read from stderr
        self.stderrq = bytearray()
        # chunks of text to be written to stdin
        self.stdinq = collections.deque()
        # requests not yet satisfied
        self.pendingq = collections.deque()
        
        self.init_req = REPL.Request(self)
        self.pendingq.append(self.init_req)
        self.block_for(self.init_req)


     def call(self,text,stderr=False):
        text_bytes = text.encode()
        self.stdinq.append(struct.pack("N",len(text_bytes)) + text_bytes)
        future = self.loop.create_future() if self.is_async else None
        request = REPL.Request(self,future=future)
        self.pendingq.append(request)
        self._sync_nonblock()
        if len(self.stdinq)>0 and self.is_async:
            self.loop.add_writer(self.proc.stdin,self._async_writer)
        return request

     def make_async(self):
        self.loop = aio.get_running_loop()
        self.is_async = True
        self.loop.add_reader(self.proc.stdout,self._sync_nonblock)
        self.loop.add_reader(self.proc.stderr,self._sync_nonblock)

     def _async_writer(self):
        self._sync_nonblock()
        if (len(self.stdinq)==0):
            self.loop.remove_writer(self.proc.stdin)

     def _sync_nonblock(self):
        stdout = self.proc.stdout.read()
        if stdout is not None:
            self.stdoutq.extend(stdout)
            if self.verbose:
                sys.stdout.write("<STDOUT>\n"+stdout.decode()+"\n</STDOUT>\n")
                sys.stdout.flush()

        stderr = self.proc.stderr.read()
        if stderr is not None:
            self.stderrq.extend(stderr)
            if self.verbose:
                sys.stdout.write("<STDERR>\n" + stderr.decode()+"\n</STDERR>\n")
                sys.stdout.flush()

        pattern = re.compile((fr"(.*?)<{self.prng.peek()}>").encode(),flags=re.S)
        if (self.verbose):
            print("looking for ",pattern)

        m1 = pattern.match(self.stdoutq)
        m2 = pattern.match(self.stderrq)

        finished = []

        #print(self.stdoutq,self.stderrq)
        
        while m1 is not None and m2 is not None:
            if (self.verbose):
                print("match!")
            self.prng()
            # we have an entire response in memory.
            # taking care of it now.
            result_stdout = m1.group(1)
            result_stderr = m2.group(1)

            self.stdoutq = self.stdoutq[m1.span()[1]:]
            self.stderrq = self.stderrq[m2.span()[1]:]

            req = self.pendingq.popleft()
            if self.is_async:
                req.future.set_result((result_stdout,result_stderr))
            else:
                req.result = (result_stdout,result_stderr)
            
            finished.append(req)

            pattern = re.compile((fr"(.*?)<{self.prng.peek()}>").encode(),flags=re.S)

            m1 = pattern.match(self.stdoutq)
            m2 = pattern.match(self.stderrq)
       
        
        try:
            while len(self.stdinq)>0:
                chunk = self.stdinq.popleft()
                self.proc.stdin.write(chunk)
                if (self.verbose):
                    sys.stdout.write("<STDIN>\n"+str(chunk)+"\n</STDIN>\n")
        except BlockingIOError as e:
            if(self.verbose):
                print("partial chunk write! weird.")
            self.stdinq.appendleft(chunk[e.characters_written:])

        try:
            self.proc.stdin.flush()
        except BlockingIOError as e:
            pass
        except BrokenPipeError as e:
            # i think the process is dead??
            self.loop.remove_reader(self.proc.stdin)
            return []

        return finished

     def block_for(self,req):
        finished = self._sync_nonblock()
        while req not in finished and not hasattr(req,"result"):
            # wait for something to read
            # or for us to be able to write, if we 
            # have things to write.
            select.select([self.proc.stdout,self.proc.stderr],
                    [self.proc.stdin] if len(self.stdinq)>0 else [],
                    [])
            finished = self._sync_nonblock()

     def close(self):
         if (self.is_async):
             self.loop.remove_writer(self.proc.stdin)
             self.loop.remove_reader(self.proc.stdout)
             self.loop.remove_reader(self.proc.stderr)
             for x in self.pendingq:
                 x.future.set_result((None,None))

         # this usually convinces coqtop to close.
         self.proc.stdin.close()
         self.proc.stdout.close()
         self.proc.stderr.close()
         self.proc.wait()

if __name__=="__main__":
    """ simple tests """

    r = REPL("coqtop",verbose=False)

    @xroutine
    def test(r):
        n = 100000
        #futures = [r.call(f"Definition v{x} := True.\n") for x in range(n)]
        #for i,x in zip(range(n),futures):
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



    import time

    import asyncio as aio


    for t in [test,test2,test3]:
        stamp = time.time()
        r = REPL("coqtop")
        t(r).block()
        r = REPL("coqtop")
        async def wrap(r):
            r.make_async()
            await t(r)
        print(time.time()-stamp)

