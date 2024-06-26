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

        self.pattern = re.compile(fr"<(\d+)>".encode())

        self.init_req = REPL.Request(self)
        self.pendingq.append(self.init_req)
        self.block_for(self.init_req)




     def call(self,text,stderr=False):
        text_bytes = text.encode()
        # were things already pending before we made the request?
        were_things_pending = len(self.stdinq)>0
        self.stdinq.append(struct.pack("N",len(text_bytes)) + text_bytes)
        future = self.loop.create_future() if self.is_async else None
        request = REPL.Request(self,future=future)
        self.pendingq.append(request)
        if self.is_async and not were_things_pending:
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


        m1 = list(re.finditer(self.pattern,self.stdoutq))
        m2 = list(re.finditer(self.pattern,self.stderrq))
        
        m1_strings = [x.group(1) for x in m1]
        m2_strings = [x.group(1) for x in m2]

        found_ids = set(m1_strings).intersection(m2_strings)

        if len(found_ids)>0 and self.verbose:
            print("found",found_ids)

        cursor1 = 0
        cursor2 = 0
        
        finished = []
        
         
        while str(self.prng.peek()).encode() in found_ids:
            target = str(self.prng.peek()).encode()
            if (self.verbose):
                print("match!")
            
            # we have an entire response in memory.
            # taking care of it now.
            m1_index = m1_strings.index(target)
            m2_index = m2_strings.index(target)

            result_stdout = self.stdoutq[cursor1:m1[m1_index].start()]
            result_stderr = self.stderrq[cursor2:m2[m2_index].start()]

            cursor1 = m1[m1_index].end()
            cursor2 = m2[m2_index].end()

            
            self.prng()
            req = self.pendingq.popleft()
            if self.is_async:
                try:
                    req.future.set_result((result_stdout,result_stderr))
                except aio.exceptions.InvalidStateError:
                    # uh huh, we're just going to move on.
                    continue
            else:
                req.result = (result_stdout,result_stderr)
            
            finished.append(req)
        
        self.stdoutq = self.stdoutq[cursor1:]
        self.stderrq = self.stderrq[cursor2:]
        
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

     def close(self,kill=False):
         if (self.is_async):
             try:
                 self.loop.remove_reader(self.proc.stdout)
                 self.loop.remove_reader(self.proc.stderr)
                 self.loop.remove_writer(self.proc.stdin)
             except ValueError:
                 # maybe already closed???
                 # happens when one of self.proc.* is not
                 # currently a valid file...
                 pass
             for x in self.pendingq:
                 try:
                     x.future.set_result((None,None))
                 except aio.exceptions.InvalidStateError:
                     # this is already dead
                     continue

         # this usually convinces coqtop to close.
         self.proc.stdin.close()
         self.proc.stdout.close()
         self.proc.stderr.close()
         if kill:
             self.proc.kill()
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

