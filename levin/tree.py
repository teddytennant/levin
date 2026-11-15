"""The search state: claims, sketches, what is believed about them, and which
step to take next.

A claim is a closed Lean proposition. A sketch is a Lean-checked reduction of
a claim to lemmas, which are claims too, shared by statement. The root is a
set of mutually exclusive resolutions: P and ¬P, or P with a guessed answer.

Per claim, t is the chance it is true. Given it is true, the chance one
prove task lands is p ~ Beta(a, b), which starts at mean `prove_rate` with
`strength` attempts' weight and counts failures. A failed attempt is one
observation with likelihood 1 - t p, so t and b move together.

S(c) is the chance c gets proved: by direct attempts within `horizon` tries,
t (1 - E[(1-p)^H]), or by any sketch, worth the product of its lemmas,
taken as independent. That is a heuristic: lemmas of one sketch fail
together more often than it says. A sketch whose lemmas have all survived a
counterexample search makes c at least as likely true as all of them, so t(c)
is raised to that product, which also moves belief off the other side of the
root. S(root) is the sum over resolutions, since at most one can be true. The
next step is the one with the largest dS(root) per token, found with one
backward pass over the DAG. New lemmas are searched for counterexamples
before anything else.
"""
import hashlib
import re
from fractions import Fraction
from math import prod

LEMMA = re.compile(r"\bL_[0-9a-f]{12}\b")

DEFAULTS = {
    "truth": 0.5,
    "lemma_truth": 0.6,
    "root_rate": 0.3,
    "prove_rate": 0.3,
    "strength": 2.0,
    "sketch_rate": 0.5,
    "catch": 0.5,
    "horizon": 3,
    "max_depth": 6,
    "max_sketches": 3,
    "max_lemmas": 4,
    "max_guesses": 4,
    "guess_value": 0.05,
    "tokens": {"prove": 60000, "falsify": 30000, "decompose": 60000, "guess": 30000},
}


def normal(text):
    return " ".join(text.split())


def key(statement):
    return hashlib.sha256(normal(statement).encode()).hexdigest()[:12]


def negate(statement):
    return f"¬({statement})"


def clamp(x, lo=0.02, hi=0.98):
    return min(hi, max(lo, x))


class Tree:
    def __init__(self, problem):
        self.problem = problem
        self.cfg = {k: problem.get(k, v) for k, v in DEFAULTS.items()}
        self.cfg["tokens"] = {**DEFAULTS["tokens"], **problem.get("tokens", {})}
        self.claims = {}
        self.sketches = {}
        self.roots = []
        self.library = []
        self.guesses = 0
        statement = problem["statement"]
        if "ANSWER" in statement:
            return
        p = self.add(statement, clamp(self.cfg["truth"], 0, 1), 0, falsified=True, rate=self.cfg["root_rate"])
        self.roots.append(p["key"])
        if p["t"] < 1:
            n = self.add(negate(statement), 1 - p["t"], 0, falsified=True, rate=self.cfg["root_rate"])
            p["pair"], n["pair"] = n["key"], p["key"]
            self.roots.append(n["key"])

    def add(self, statement, t, depth, falsified=False, rate=None):
        k = key(statement)
        if k not in self.claims:
            self.claims[k] = {
                "key": k, "statement": normal(statement), "status": "open", "t": t, "rate": rate or self.cfg["prove_rate"],
                "fails": 0, "sketch_fails": 0, "falsified": falsified, "depth": depth,
                "sketches": [], "proof": None, "notes": "",
            }
        c = self.claims[k]
        c["depth"] = min(c["depth"], depth)
        return c

    # beliefs

    def beta(self, c):
        m, n = c["rate"], self.cfg["strength"]
        return m * n, (1 - m) * n + c["fails"]

    def p(self, c):
        a, b = self.beta(c)
        return a / (a + b)

    def reach(self, c):
        """Chance `horizon` more attempts prove c if it is true: 1 - E[(1-p)^H]."""
        a, b = self.beta(c)
        return 1 - prod((b + i) / (a + b + i) for i in range(self.cfg["horizon"]))

    def set_t(self, c, t):
        c["t"] = t
        if "pair" in c:
            self.claims[c["pair"]]["t"] = 1 - t
        for sk in self.sketches.values():
            parent = self.claims[sk["claim"]]
            if c["key"] in sk["lemmas"] and parent["status"] == "open" and self.bound(parent) > parent["t"]:
                self.set_t(parent, self.bound(parent))

    def bound(self, c):
        """How likely c is true given its sketches: each one whose lemmas all
        survived a counterexample search makes c at least as likely as all of
        them. A lemma not yet proved counts for no more than `lemma_truth`, so a
        decomposer's confidence cannot move the root by itself."""
        best = 0.0
        for s in self.live(c):
            lemmas = [self.claims[x] for x in self.sketches[s]["lemmas"]]
            if all(x["falsified"] or x["status"] != "open" for x in lemmas):
                best = max(best, prod(1.0 if x["status"] == "proved" else min(x["t"], self.cfg["lemma_truth"]) for x in lemmas))
        return best

    def live(self, c):
        return [s for s in c["sketches"] if all(self.claims[x]["status"] != "refuted" for x in self.sketches[s]["lemmas"])]

    def fresh_sketch(self):
        """What a sketch not yet seen is worth: two fresh lemmas."""
        c = {"rate": self.cfg["prove_rate"], "fails": 0}
        return (self.cfg["lemma_truth"] * self.reach(c)) ** 2

    # values

    def order(self):
        """Claims reachable from the roots, each after everything below it."""
        seen, out = set(), []

        def visit(k):
            if k in seen:
                return
            seen.add(k)
            c = self.claims[k]
            if c["status"] == "open":
                for s in c["sketches"]:
                    for child in self.sketches[s]["lemmas"]:
                        visit(child)
            out.append(k)

        for r in self.roots:
            visit(r)
        return out

    def values(self, order):
        S = {}
        for k in order:
            c = self.claims[k]
            if c["status"] != "open":
                S[k] = 1.0 if c["status"] == "proved" else 0.0
                continue
            miss = 1 - c["t"] * self.reach(c)
            for s in c["sketches"]:
                miss *= 1 - prod(S[x] for x in self.sketches[s]["lemmas"])
            S[k] = 1 - miss
        return S

    def grads(self, order, S):
        """dS(root)/dS(c) for every claim."""
        g = dict.fromkeys(order, 0.0)
        for r in self.roots:
            g[r] = 1.0
        for k in reversed(order):
            c = self.claims[k]
            if c["status"] != "open" or not g[k]:
                continue
            lemmas = [self.sketches[s]["lemmas"] for s in c["sketches"]]
            hs = [prod(S[x] for x in ls) for ls in lemmas]
            for i, ls in enumerate(lemmas):
                dh = g[k] * (1 - c["t"] * self.reach(c)) * prod(1 - h for j, h in enumerate(hs) if j != i)
                for j, x in enumerate(ls):
                    g[x] += dh * prod(S[y] for m, y in enumerate(ls) if m != j)
        return g

    def solved(self):
        return next((k for k in self.roots if self.claims[k]["status"] == "proved"), None)

    def chance(self):
        order = self.order()
        S = self.values(order)
        return min(1.0, sum(S[r] for r in self.roots))

    # choosing

    def actions(self, busy=()):
        """Every step worth taking, best first: (score, kind, claim key).
        Counterexample searches come before everything else."""
        order = self.order()
        S = self.values(order)
        g = self.grads(order, S)
        cost = self.cfg["tokens"]
        out = []
        for k in order:
            c = self.claims[k]
            if c["status"] != "open" or k in busy or g[k] <= 0:
                continue
            gain = g[k] * (1 - S[k])
            land = c["t"] * self.p(c)
            if not c["falsified"]:
                out.append((gain / cost["falsify"], "falsify", k))
                continue
            out.append((gain * land / cost["prove"], "prove", k))
            if c["depth"] < self.cfg["max_depth"] and len(self.live(c)) < self.cfg["max_sketches"]:
                n = self.cfg["strength"]
                valid = self.cfg["sketch_rate"] * n / (n + c["sketch_fails"])
                out.append((gain * valid * c["t"] * self.fresh_sketch() / cost["decompose"], "decompose", k))
        if "ANSWER" in self.problem["statement"] and self.guesses < self.cfg["max_guesses"] and "guess" not in busy:
            left = 1 - min(1.0, sum(S[r] for r in self.roots))
            out.append((left * self.cfg["guess_value"] / cost["guess"], "guess", None))
        return sorted(out, key=lambda a: (a[1] != "falsify", -a[0]))

    # outcomes

    def fail(self, kind, k):
        """A verifier said no. Evidence, unlike a crash or a rate limit."""
        if kind == "guess":
            self.guesses += 1
            return
        c = self.claims[k]
        if kind == "prove":
            land = c["t"] * self.p(c)
            self.set_t(c, max(self.bound(c), c["t"] * (1 - self.p(c)) / (1 - land)))
            c["fails"] += 1
        elif kind == "falsify":
            miss = 1 - self.cfg["catch"]
            c["falsified"] = True
            self.set_t(c, c["t"] / (c["t"] + (1 - c["t"]) * miss))
        elif kind == "decompose":
            c["sketch_fails"] += 1

    def entry(self, name, statement, text, uses):
        self.library.append({"name": name, "statement": statement, "text": text, "deps": sorted(set(LEMMA.findall(uses)))})

    def proved(self, k, body):
        c = self.claims[k]
        if c["status"] != "open":
            return
        self.entry(f"L_{k}", c["statement"], f"theorem L_{k} : {c['statement']} := {body}", body)
        c["proof"] = body
        self.settle(k)

    def refuted(self, k, body):
        """A proof of ¬c. For a root, that proves the other side."""
        c = self.claims[k]
        if c["status"] != "open":
            return
        n = key(negate(c["statement"]))
        self.entry(f"L_{n}", normal(negate(c["statement"])), f"theorem L_{n} : {normal(negate(c['statement']))} := {body}", body)
        c["status"], c["proof"] = "refuted", body
        self.set_t(c, 0.0)
        for sk in self.sketches.values():
            if k in sk["lemmas"]:
                parent = self.claims[sk["claim"]]
                parent["notes"] += f"\n\nA plan for this claim needed `{c['statement']}`, which is false. Its refutation:\n{body[:1500]}\n"
        if c.get("pair") == n:
            self.claims[n]["proof"] = body
            self.settle(n)
        elif "pair" in c:
            other = self.claims[c["pair"]]
            self.entry(f"L_{other['key']}", other["statement"],
                       f"theorem L_{other['key']} : {other['statement']} := Classical.byContradiction L_{n}", f"L_{n}")
            other["proof"] = f"Classical.byContradiction L_{n}"
            self.settle(other["key"])

    def settle(self, k):
        c = self.claims[k]
        if c["status"] != "open":
            return
        c["status"] = "proved"
        self.set_t(c, 1.0)
        if "pair" in c:
            self.claims[c["pair"]]["status"] = "refuted"
        for s, sk in list(self.sketches.items()):
            if k in sk["lemmas"]:
                self.try_sketch(s)

    def try_sketch(self, s):
        sk = self.sketches[s]
        parent = self.claims[sk["claim"]]
        if parent["status"] != "open" or any(self.claims[x]["status"] != "proved" for x in sk["lemmas"]):
            return
        p, args = parent["key"], " ".join(f"L_{x}" for x in sk["lemmas"])
        binders = " ".join(f"(h{i + 1} : {t})" for i, t in enumerate(sk["texts"]))
        text = (f"theorem R_{s} {binders} : {parent['statement']} := {sk['body']}\n\n"
                f"theorem L_{p} : {parent['statement']} := R_{s} {args}")
        self.entry(f"L_{p}", parent["statement"], text, " ".join([sk["body"], *sk["texts"], args]))
        parent["proof"] = {"sketch": s}
        self.settle(p)

    def ancestors(self, k):
        up, todo = set(), [k]
        while todo:
            x = todo.pop()
            if x in up:
                continue
            up.add(x)
            todo += [sk["claim"] for sk in self.sketches.values() if x in sk["lemmas"]]
        return up

    def sketched(self, k, sketch):
        """Add a sketch Lean accepted. False if it would make a cycle."""
        c = self.claims[k]
        texts, credences = [], []
        for x in sketch["lemmas"]:
            texts.append(normal(x["statement"] if isinstance(x, dict) else x))
            credences.append(x.get("credence") if isinstance(x, dict) else None)
        keys = [key(t) for t in texts]
        if set(keys) & self.ancestors(k):
            c["sketch_fails"] += 1
            return False
        for t, credence in zip(texts, credences):
            prior = self.cfg["lemma_truth"] if not isinstance(credence, (int, float)) else clamp(credence, 0.1, 0.9)
            self.add(t, prior, c["depth"] + 1)
        s = f"{k}_{len(c['sketches'])}"
        self.sketches[s] = {"claim": k, "lemmas": list(dict.fromkeys(keys)), "texts": texts,
                            "body": sketch["body"], "informal": str(sketch.get("informal", ""))}
        c["sketches"].append(s)
        self.try_sketch(s)
        return True

    def guessed(self, answer, credence):
        self.guesses += 1
        answer = str(Fraction(answer))
        statement = self.problem["statement"].replace("ANSWER", f"({answer})")
        prior = clamp(credence, 0.05, 0.9) if isinstance(credence, (int, float)) else self.cfg["lemma_truth"]
        c = self.add(statement, prior, 0, rate=self.cfg["root_rate"])
        if c["key"] not in self.roots:
            self.roots.append(c["key"])
        return c

    def certificate(self):
        """One Lean file proving the resolution, from the library."""
        k = self.solved()
        if k is None:
            return None
        by_name = {e["name"]: e for e in self.library}
        need, todo = set(), [f"L_{k}"]
        while todo:
            n = todo.pop()
            if n in by_name and n not in need:
                need.add(n)
                todo += by_name[n]["deps"]
        body = "".join(e["text"] + "\n\n" for e in self.library if e["name"] in need)
        return (f"{self.problem.get('preamble', '')}\n\nset_option autoImplicit false\n\n{body}"
                f"theorem levin_root : {self.claims[k]['statement']} := L_{k}\n")
