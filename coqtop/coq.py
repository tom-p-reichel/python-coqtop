import asyncio
import secrets
import re
import glob
from pathlib import Path
import os
import warnings
import string
from .repl import REPL

class CoqProcess:
        
    def __init__(self,*args,verbose=False):
        self.lock = asyncio.Lock()
        self.p = REPL("coqtop",*args,verbose=verbose)
        # TODO: make coqprocess optional async too.
        self.p.make_async()
        self.env_regex = re.compile(r"^([^\s]+):([^\n]*\n(?:[\t\s]+[^\n]+(?:\n|$))*)",flags=re.MULTILINE)

    def close(self,**kwargs):
        self.p.close(**kwargs)


    async def run(self, proofscript, return_stderr=False):
        """ asynchronously run a coq snippet, receive stdout for that snippet """
        stdout,stderr = await self.p.call(proofscript+"\n")
        if stdout is None:
            warnings.warn(f"Tried to run {proofscript} but got None?!")
            return (None,None) if return_stderr else None
        return (stdout.decode(),stderr.decode()) if return_stderr else stdout.decode()
    
    async def done(self):
        output,stderr = await self.run("try idtac.",return_stderr=True)
        return "Error" in stderr

    async def environment(self,types=["Theorem","Lemma","Definition","Method","Instance","Axiom"],everything=False ):
        """ grab a set of all (?) defined things in the environment"""
        thms = {}
        
        if everything:
            searches = [self.run(f"Search \"{string.ascii_letters[i]}\" " + " ".join(f"-\"{string.ascii_letters[j]}\"" for j in range(i)) + ".") for i in range(len(string.ascii_letters))]
        else:
            searches = [self.run(f"Search is:{t}.") for t in types]

        

        for s in searches:
            cthms = await s
            thms.update(re.findall(self.env_regex, cthms))
        if types:
            return thms
        else:
            return set(thms.keys())

    async def locate(self,term):
        """ attempt to find the full path of a term """
        out = await self.run(f"Locate {term}.")
        if "No object of" in out:
            return None
        else:
            try:
                match = [x for x in out.split() if "." in x][0]
                return match
            except IndexError:
                warnings.warn(f"Couldn't locate {term}, got: {out}")

def guess_switch():
    try:
        return os.environ["OPAM_SWITCH_PREFIX"]
    except KeyError:
        raise OSError("Couldn't find a switch! Did you `eval $(opam env)`? Is OPAM_SWITCH_PREFIX set?")
        

async def test():
    p = await CoqProcess.init()
    out = await p.run("Check (1+1).")
    out2 = await p.run("Compute (1+1).")
    await p.run("Theorem easy: True.")
    assert await p.done() == False
    await p.run("intros. auto.")
    assert await p.done() == True
    await p.run("Qed.")
    print(out)
    print(out2)
    print(await p.locate("or_comm"))


async def import_all(exclude=None,require_import=False,**kwargs):
    
    searchdir = guess_switch()+"/lib/coq/"

    if (not exclude):
        exclude = set()

    paths = {".".join(Path(x).relative_to(searchdir).parts[1:])[:-2] for x in glob.glob(searchdir+"/**/*.v",recursive=True)}
    
    p = CoqProcess(**kwargs)
    
    for x in paths:
        if (x in exclude):
            continue
        try:
            await asyncio.wait_for(asyncio.shield(p.run(f"Require Import {x}." if require_import else f"Require {x}.")),3.0)
        except asyncio.exceptions.TimeoutError:
            # something's wrong with that.
            exclude.add(x)
            p.close()
            return await import_all(exclude=exclude)
     
    return (p, exclude)


async def locate_import(candidate,instance=None):
    # todo: rewrite this.
    fully_qualified_import = ""
    suffix = candidate
    if instance is None:
        p = CoqProcess(**kwargs)
    else:
        p = instance
    while suffix != "":
        prefix, _, suffix = suffix.partition(".")
        fully_qualified_import += prefix + "."
        await p.run(f"Require {fully_qualified_import}")
        if await p.locate(candidate):
            if instance is None:
                p.close()
            return fully_qualified_import[:-1]
    if instance is None:
        p.close()
    warnings.warn(f"couldn't find an import for {candidate}")

if __name__=="__main__":
    l = asyncio.get_event_loop()
    l.run_until_complete(test())
    

