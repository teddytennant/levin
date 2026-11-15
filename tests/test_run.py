import io
import json
import os
import tempfile
import unittest

from levin.run import Run, init
from levin.tree import key


class FakeInlet:
    """Runs a task the moment it is asked whether it settled. `work` maps a
    task to (ok, reason, files it leaves behind)."""

    def __init__(self, work, judge=lambda claim, files: True):
        self.work, self.judge = work, judge
        self.tasks, self.workdirs, self.killed = {}, {}, []

    def submit(self, worker, goal, verify, files, tokens, retries, memory_mb=None):
        id = f"t{len(self.tasks)}"
        self.tasks[id] = (worker, json.loads(files["claim.json"]), files)
        return id

    def settled(self, ids):
        out = {}
        for id in ids:
            worker, claim, files = self.tasks[id]
            if worker == "levin_check":
                verdict = self.judge(claim, files)
                ok, reason = verdict if isinstance(verdict, tuple) else (verdict, "verifier")
                out[id] = {"ok": ok, "reason": reason, "used": 0, "last": id}
                continue
            ok, reason, left = self.work(claim)
            self.workdirs[id] = left
            out[id] = {"ok": ok, "reason": reason, "used": 100, "last": id}
        return out

    def kill(self, id):
        self.killed.append(id)

    def read(self, id, name):
        return self.workdirs.get(id, {}).get(name)


def worker(claim):
    """Splits P into A and B, proves A and B, finds no counterexamples."""
    s = claim["statement"]
    if claim["kind"] == "sketch" and s == "P":
        return True, "ok", {"sketch.json": json.dumps({"lemmas": ["A", "B"], "body": "h1 h2", "informal": "split"}),
                            "notes.md": "split it"}
    if claim["kind"] == "prove" and s in ("A", "B"):
        return True, "ok", {"proof.lean": f"proof_{s}"}
    return False, "verifier", {"notes.md": f"no luck on {s}"}


class RunTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.problem()

    def problem(self, **more):
        path = os.path.join(self.dir, "p.json")
        with open(path, "w") as f:
            json.dump({"statement": "P", "truth": 1.0, "root_rate": 0.01, "inlet": {"slots": 2}, **more}, f)
        self.run_dir = tempfile.mkdtemp(dir=self.dir)
        os.rmdir(self.run_dir)
        init(path, self.run_dir)

    def run_with(self, inlet, steps=40):
        run = Run(self.run_dir, inlet, out=io.StringIO())
        for _ in range(steps):
            if not run.step():
                break
        return run

    def test_splits_proves_and_certifies(self):
        inlet = FakeInlet(worker)
        run = self.run_with(inlet)
        t = run.tree
        self.assertEqual(t.solved(), key("P"))
        self.assertTrue(run.certified)
        with open(os.path.join(self.run_dir, "cert.lean")) as f:
            self.assertIn(f"theorem levin_root : P := L_{key('P')}", f.read())
        kinds = [(w, c["kind"], c["statement"]) for w, c, _ in inlet.tasks.values()]
        self.assertIn(("prover", "prove", "¬(A)"), kinds)
        self.assertLess(kinds.index(("prover", "prove", "¬(A)")), kinds.index(("prover", "prove", "A")))
        self.assertEqual(kinds[-1], ("levin_check", "cert", "P"))

    def test_one_task_per_claim(self):
        inlet = FakeInlet(worker)
        run = Run(self.run_dir, inlet, out=io.StringIO())
        run.collect = lambda: None
        run.step()
        self.assertEqual([c["statement"] for _, c, _ in inlet.tasks.values()], ["P"])

    def test_restart_rebuilds_the_same_tree(self):
        run = self.run_with(FakeInlet(worker), steps=4)
        again = Run(self.run_dir, FakeInlet(worker), out=io.StringIO())
        self.assertEqual(again.tree.claims, run.tree.claims)
        self.assertEqual(again.inflight, run.inflight)
        self.assertEqual(again.spent, run.spent)

    def test_judge_overrules_the_cell(self):
        inlet = FakeInlet(worker, judge=lambda claim, files: claim["kind"] != "sketch")
        run = self.run_with(inlet, steps=6)
        self.assertEqual(run.tree.sketches, {})
        self.assertGreater(run.tree.claims[key("P")]["sketch_fails"], 0)

    def test_a_prove_task_can_disprove(self):
        def disprover(claim):
            if claim["kind"] == "prove" and claim["statement"] == "P":
                return True, "ok", {"negation.lean": "counterexample"}
            return False, "verifier", {}

        self.problem(truth=0.5)
        inlet = FakeInlet(disprover)
        run = self.run_with(inlet)
        self.assertEqual(run.tree.claims[run.tree.solved()]["statement"], "¬(P)")
        judged = [(c["kind"], c["statement"]) for w, c, _ in inlet.tasks.values() if w == "levin_check"]
        self.assertIn(("prove", "¬(P)"), judged)

    def test_a_crashed_judge_is_asked_again(self):
        crashes = []

        def judge(claim, files):
            if claim["kind"] == "sketch" and not crashes:
                crashes.append(1)
                return False, "crash"
            return True

        run = self.run_with(FakeInlet(worker, judge))
        self.assertEqual(run.tree.solved(), key("P"))
        self.assertEqual(run.tree.claims[key("P")]["sketch_fails"], 0)

    def test_failures_without_a_verdict_are_not_evidence(self):
        run = self.run_with(FakeInlet(lambda claim: (False, "exit", {})), steps=5)
        p = run.tree.claims[key("P")]
        self.assertEqual((p["fails"], p["sketch_fails"]), (0, 0))
        self.assertGreater(run.paused_until, 0)

    def test_notes_carry_over(self):
        run = self.run_with(FakeInlet(worker), steps=5)
        notes = {c["statement"]: c["notes"] for c in run.tree.claims.values()}
        self.assertEqual((notes["P"], notes["A"]), ("split it", "no luck on ¬(A)"))

    def test_budget_stops_new_work(self):
        with open(os.path.join(self.run_dir, "events.jsonl")) as f:
            first = json.loads(f.readline())
        first["problem"]["budget"] = 50000
        with open(os.path.join(self.run_dir, "events.jsonl"), "w") as f:
            f.write(json.dumps(first) + "\n")
        inlet = FakeInlet(worker)
        run = self.run_with(inlet)
        self.assertEqual(inlet.tasks, {})
        self.assertEqual(run.inflight, {})
        self.assertIsNone(run.tree.solved())


if __name__ == "__main__":
    unittest.main()
