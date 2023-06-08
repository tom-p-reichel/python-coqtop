import subprocess
import pathlib
import os
import queue


preloaders = list(pathlib.Path(__file__).parent.glob("preloadtricks*so"))

assert len(preloaders)==1, "preloadtricks shared object missing. Did this library build correctly?"

preload = preloaders[0]

class REPL():
    class Request():
        def __init__(self,repl):
            self.repl = repl

    def __init__(self,command,*args):
        new_env = os.environ.copy()
        new_env["LD_PRELOAD"] = preload
        self.proc = subprocess.Popen([command]+list(args),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,env=new_env)
        os.set_blocking(self.proc.stdin.fileno(),False)
        os.set_blocking(self.proc.stdout.fileno(),False)
        os.set_blocking(self.proc.stderr.fileno(),False)
        self.in_queue = queue.Queue()
        self.out_queue = queue.Queue()

    def run(self,cmd):
        self.in_queue.put(cmd)
        self._sync_nonblock()

    def _sync_nonblock(self,cmd):
        
        


