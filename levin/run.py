"""The loop: pick the steepest step, run it on inlet, judge it, repeat.

Everything levin knows is in <dir>/events.jsonl. The tree is rebuilt from it
on every start, so a killed run picks up where it stopped, and tasks still on
inlet are collected when they finish.
"""
import json
import os
import sys
import time

from . import prompts
from .inlet import Inlet
from .tree import Tree, negate

CHECK = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check.py")
ARTIFACT = {"prove": "proof.lean", "falsify": "proof.lean", "decompose": "sketch.json", "formalize": "glue.lean",
            "guess": "answer.json", "cert": "cert.lean"}
MERITS = {"verifier", "purse", "timeout", "stall", "exit"}
GATE = {"prove": "prove", "falsify": "prove", "decompose": "sketch", "formalize": "glue", "search": "score",
        "guess": "prop", "cert": "cert"}


class Run:
    def __init__(self, dir, inlet=None, out=sys.stdout):
        self.dir = dir
        self.out = out
        self.path = os.path.join(dir, "events.jsonl")
        with open(self.path) as f:
            events = [json.loads(line) for line in f if line.strip()]
        self.problem = events[0]["problem"]
        self.cfg = self.problem.get("inlet", {})
        self.inlet = inlet or Inlet(self.cfg.get("bin", "inlet"), self.cfg.get("home"))
        self.tree = Tree(self.problem)
        self.inflight = {}
        self.spent = 0
        self.certified = None
        for e in events[1:]:
            self.apply(e)
        if self.certified is False:
            self.certified = None
        self.idle_failures = 0
        self.paused_until = 0

    def record(self, e):
        with open(self.path, "a") as f:
            f.write(json.dumps(e) + "\n")
            f.flush()
            os.fsync(f.fileno())
        self.apply(e)

    def artifact(self, kind):
        if kind == "search":
            return self.problem["score"].get("file", "candidate.py")
        return ARTIFACT[kind]

    def apply(self, e):
        if e["ev"] == "submit":
            self.inflight[e["id"]] = e
            if e["phase"] == "work":
                self.tree.picked(e["kind"], e["claim"])
            return
        self.inflight.pop(e["id"], None)
        self.spent += e.get("used", 0)
        kind, k, outcome = e["kind"], e.get("claim"), e.get("outcome")
        if e.get("notes") and k in self.tree.claims:
            c = self.tree.claims[k]
            c["notes"] = (c["notes"] + e["notes"])[-8000:]
        if outcome == "rejected":
            self.tree.fail(kind, k)
        elif outcome == "accepted":
            a = e["artifact"]
            if kind == "prove":
                self.tree.proved(k, a.strip())
            elif kind == "falsify":
                self.tree.refuted(k, a.strip())
            elif kind == "decompose":
                self.tree.sketched(k, json.loads(a))
            elif kind == "formalize":
                self.tree.formalized(k, a.strip())
            elif kind == "search":
                self.tree.searched(k, a, e["score"])
            elif kind == "guess":
                a = json.loads(a)
                self.tree.guessed(str(a["answer"]).strip(), a.get("credence"))
            elif kind == "cert":
                self.certified = True
        elif outcome == "cert-failed":
            self.certified = False

    def say(self, *parts):
        print(time.strftime("%H:%M:%S"), *parts, file=self.out, flush=True)

    # tasks

    def claim_json(self, kind, k):
        p, t = self.problem, self.tree
        if kind == "guess":
            statement = p["statement"]
        elif kind == "cert":
            statement = t.claims[t.solved()]["statement"]
        elif kind == "falsify":
            statement = negate(t.claims[k]["statement"])
        elif kind == "formalize":
            statement = t.claims[t.sketches[k]["claim"]]["statement"]
        else:
            statement = t.claims[k]["statement"]
        return json.dumps({
            "kind": GATE[kind], "statement": statement, "preamble": p.get("preamble", ""),
            "lean": p.get("lean", ["lean"]), "lean_dir": p.get("lean_dir"),
            "leanchecker": p.get("leanchecker", ["leanchecker"]), "timeout": p.get("lean_timeout", 600),
            "max_lemmas": t.cfg["max_lemmas"], "library": t.library,
            "negation": negate(statement) if kind == "prove" else None,
            "fresh": p.get("fresh", False),
            "answer_type": p.get("answer_type"),
            "root": p.get("statement", ""), "defs": t.defs,
            "lemmas": t.sketches[k]["texts"] if kind == "formalize" else None,
            "score": p.get("score") if kind == "search" else None,
        }, indent=1)

    def verify(self):
        return f"python3 {self.cfg.get('check', CHECK)} claim.json"

    def start(self, kind, k, score=0.0):
        notes = self.tree.claims[k]["notes"] if k in self.tree.claims and self.problem.get("notes", True) else ""
        goal = prompts.goal(self.tree, kind, k, self.cfg.get("check", CHECK))
        tokens = self.tree.cfg["tokens"][kind]
        worker = self.cfg.get("workers", {}).get(kind, self.cfg.get("worker", "prover"))
        files = {"claim.json": self.claim_json(kind, k), "notes.md": notes}
        if kind == "search":
            best = self.tree.claims[k]["best"] if self.problem.get("notes", True) else []
            files["best.json"] = json.dumps(best, indent=1)
        id = self.inlet.submit(worker, goal, self.verify(), files,
                               tokens, self.cfg.get("retries", 1), self.cfg.get("memory_mb", 8192))
        self.record({"ev": "submit", "id": id, "kind": kind, "claim": k, "phase": "work", "tokens": tokens, "seeded": notes})
        self.say(f"{kind:9}", label(k), f"{score:.3g}", id)

    def judge(self, kind, k, artifact, work=None, tries=1):
        """Re-check an artifact in a fresh cell, against levin's own copy of the
        statement. The worker could have edited claim.json in its own workdir."""
        files = {"claim.json": self.claim_json(kind, k), self.artifact(kind): artifact}
        id = self.inlet.submit(self.cfg.get("checker", "levin_check"), f"levin judges {kind}", self.verify(), files,
                               1000, 0, self.cfg.get("memory_mb", 8192))
        self.record({"ev": "submit", "id": id, "kind": kind, "claim": k, "phase": "check", "artifact": artifact,
                     "work": work, "tries": tries})

    def collect(self):
        for id, r in self.inlet.settled(list(self.inflight)).items():
            e = self.inflight[id]
            kind, k = e["kind"], e["claim"]
            if e["phase"] == "check":
                if not r["ok"] and r["reason"] != "verifier":
                    self.record({"ev": "settle", "id": id, "kind": kind, "claim": k, "used": r["used"]})
                    self.say("the judge itself failed", r["reason"], kind, label(k))
                    if e.get("tries", 1) < 3:
                        self.judge(kind, k, e["artifact"], e.get("work"), e.get("tries", 1) + 1)
                    else:
                        self.say("gave up judging it; the artifact is in the event log, from task", e.get("work"))
                    continue
                if kind == "search":
                    out = self.inlet.verifier_output(r["last"]).strip().splitlines()
                    if r["ok"] and out and out[-1].startswith("score "):
                        e = dict(e, score=float(out[-1].split()[1]))
                    outcome = "accepted" if "score" in e else "rejected"
                elif kind == "cert":
                    outcome = "accepted" if r["ok"] else "cert-failed"
                else:
                    outcome = "accepted" if r["ok"] else "rejected"
                    if not r["ok"]:
                        self.say("the in-cell gate passed but the judge did not", e.get("work"))
                self.record({"ev": "settle", "id": id, "kind": kind, "claim": k, "outcome": outcome,
                             "artifact": e["artifact"], "used": r["used"], "score": e.get("score")})
                self.say(f"{outcome:9}", kind, label(k))
                continue
            notes, seeded = self.inlet.read(r["last"], "notes.md") or "", e.get("seeded", "")
            added = notes[len(seeded):] if notes.startswith(seeded) else notes
            artifact = self.inlet.read(r["last"], self.artifact(kind)) if r["ok"] else None
            if r["ok"] and artifact is None and kind == "prove":
                artifact = self.inlet.read(r["last"], "negation.lean")
                kind = "falsify" if artifact is not None else kind
            evidence = r["ok"] or (r["reason"] in MERITS and r["used"] > 0)
            outcome = None if r["ok"] or not evidence else "rejected"
            self.record({"ev": "settle", "id": id, "kind": kind, "claim": k, "outcome": outcome,
                         "used": r["used"], "reason": r["reason"], "notes": added[-4000:]})
            if artifact is not None:
                self.judge(kind, k, artifact, id)
            elif not r["ok"]:
                self.say(f"{'failed':9}", kind, label(k), r["reason"])
            self.idle_failures = 0 if evidence else self.idle_failures + 1
            if self.idle_failures >= self.cfg.get("pause_after", 3):
                self.paused_until = time.time() + self.cfg.get("pause_seconds", 900)
                self.idle_failures = 0
                self.say("pausing: tasks are failing without a verdict (rate limit? broken worker?)")

    def step(self):
        """Collect, then fill free slots. False when there is nothing left to do."""
        self.collect()
        t = self.tree
        if t.solved():
            for id, e in self.inflight.items():
                if e["phase"] == "work" and not e.get("killed"):
                    self.inlet.kill(id)
                    e["killed"] = True
            if self.certified is None and not self.inflight:
                cert = t.certificate()
                with open(os.path.join(self.dir, "cert.lean"), "w") as f:
                    f.write(cert)
                self.judge("cert", None, cert)
                self.say("resolved", t.claims[t.solved()]["statement"])
            return bool(self.inflight)
        if time.time() < self.paused_until:
            return True
        budget = self.problem.get("budget", 2_000_000)
        busy = {e["claim"] if e["kind"] != "guess" else "guess" for e in self.inflight.values()}
        reserved = sum(e.get("tokens", 0) for e in self.inflight.values() if e["phase"] == "work")
        slots = self.cfg.get("slots", 2) - sum(e["phase"] == "work" for e in self.inflight.values())
        for score, kind, k in t.actions(busy):
            if slots <= 0 or self.spent + reserved + t.cfg["tokens"][kind] > budget:
                break
            if (k or "guess") in busy:
                continue
            self.start(kind, k, score)
            busy.add(k if k else "guess")
            reserved += t.cfg["tokens"][kind]
            slots -= 1
        return bool(self.inflight)

    def loop(self, poll=5):
        while self.step():
            time.sleep(poll)
        t = self.tree
        if t.solved():
            verdict = {True: "replayed by leanchecker", False: "FAILED the replay", None: "not checked"}[self.certified]
            self.say(f"done: {t.claims[t.solved()]['statement']}; {self.dir}/cert.lean {verdict}")
        else:
            self.say(f"stopped: {self.spent} tokens spent, P(resolved) now {t.chance():.3f}")


def label(k):
    """L_<key> for a claim, the sketch id for a sketch, nothing for a guess."""
    return "" if k is None else k if "_" in k else f"L_{k}"


def show(run, top=12):
    t = run.tree
    print(f"P(resolved) {t.chance():.4f}   spent {run.spent}   in flight {len(run.inflight)}   claims {len(t.claims)}   proved {len(t.library)}")
    order = t.order()
    S = t.values(order)
    print("\nnext steps:")
    for score, kind, k in t.actions()[:top]:
        c = t.claims.get(k) or t.claims.get(t.sketches.get(k, {}).get("claim"), {})
        print(f"  {score:10.3g}  {kind:9}  {label(k)}  {c.get('statement', '')[:90]}")
    print("\nclaims:")
    for k in reversed(order):
        c = t.claims[k]
        print(f"  L_{k}  {c['status']:7} d{c['depth']} S={S[k]:.3f} t={c['t']:.2f} fails={c['fails']}  {c['statement'][:80]}")


def curve(run):
    """Tokens spent and the best score so far, one row per search result, and
    for a proof run, the tokens at which the root was settled."""
    spent, best = 0, None
    with open(run.path) as f:
        for line in f:
            e = json.loads(line)
            if e["ev"] != "settle":
                continue
            spent += e.get("used", 0)
            if e["kind"] == "search" and e.get("outcome") == "accepted":
                best = e["score"] if best is None else max(best, e["score"])
                print(f"{spent:>10} {best}")
            elif e["kind"] == "cert" and e.get("outcome") == "accepted":
                print(f"{spent:>10} settled")
    print(f"{run.spent:>10} total")


def init(problem_path, dir):
    with open(problem_path) as f:
        problem = json.load(f)
    Tree(problem)
    os.makedirs(dir, exist_ok=True)
    path = os.path.join(dir, "events.jsonl")
    if os.path.exists(path):
        sys.exit(f"{path} exists")
    with open(path, "w") as f:
        f.write(json.dumps({"ev": "problem", "problem": problem}) + "\n")
    print(f"levin run {dir}")


USAGE = """levin init <problem.json> <dir>
levin run <dir>
levin show <dir>
levin curve <dir>
levin cert <dir>"""


def main(argv=sys.argv[1:]):
    if len(argv) < 2 or argv[0] not in ("init", "run", "show", "curve", "cert") or (argv[0] == "init" and len(argv) < 3):
        sys.exit(USAGE)
    if argv[0] == "init":
        return init(argv[1], argv[2])
    run = Run(argv[1])
    if argv[0] == "run":
        run.loop()
    elif argv[0] == "show":
        show(run)
    elif argv[0] == "curve":
        curve(run)
    else:
        cert = run.tree.certificate()
        if cert is None:
            sys.exit("not resolved yet")
        print(cert)
