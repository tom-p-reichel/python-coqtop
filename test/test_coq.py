from unittest import IsolatedAsyncioTestCase
from coqtop import CoqProcess

class TestCoq(IsolatedAsyncioTestCase):
    async def test_basic(self):
        p = CoqProcess()
        out = await p.run("Check (1+1).")
        out2 = await p.run("Compute (1+1).")
        await p.run("Theorem easy: True.")
        assert await p.done() == False
        await p.run("intros. auto.")
        assert await p.done() == True
        await p.run("Qed.")



