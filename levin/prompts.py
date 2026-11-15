"""What each worker is asked to do."""

GATE = """Check your work before you stop with:

    python3 {check} claim.json

It runs the same gate that judges you. Its output is Lean's."""

SHARED = """You are one step of a proof search. The question being settled:

    {root}

Preamble every Lean file starts with:

    {preamble}

{why}
{library}
notes.md holds what earlier attempts on this claim tried and learned. Read it first.
Before you stop, add to it what you tried, what failed and why, and any idea you
did not get to, whether or not you succeeded. The next attempt reads it.

You have a shell, python3 and Lean. Use python3 to test claims on small cases
before you try to prove them.
{hints}
"""

PROVE = """Prove this claim in Lean 4:

    {statement}

Write the proof to proof.lean: only the text that comes after `:=`, a term or a
`by` block. Do not restate the theorem. Declarations, imports, notation,
#commands and set_option (other than maxHeartbeats) are rejected. Work the math
out informally first if it is not routine. If you find the claim is false,
prove its negation instead and write that to negation.lean (again only the text
after `:=`); that settles the claim just as well.

"""

FALSIFY = """This claim was proposed as a step of a proof and nobody has checked it:

    {statement}

Try to show it is false. Search for a counterexample with python3 first: small
cases, edge cases, degenerate inputs. If you find one, prove the negation in
Lean and write that proof to proof.lean (only the text after `:=`; the judge
checks `¬({statement})`). If you find nothing, write in notes.md exactly what
you searched and stop. Do not spend this task trying to prove the claim.

"""

DECOMPOSE = """Split this claim into easier lemmas:

    {statement}

Start with an informal proof. Then write sketch.json:

    {{"informal": "the informal proof, in a few paragraphs",
      "lemmas": [{{"statement": "<Lean proposition>", "credence": 0.8}}, ...],
      "body": "<Lean proof of the claim from h1 .. hk>"}}

Each lemma is a closed Lean proposition with no `by` in it. The judge checks
`theorem _ (h1 : lemma1) ... (hk : lemmak) : claim := body`, so the body may
use h1 .. hk. Between one and {max_lemmas} lemmas. Each must be strictly easier
than the claim: one that gives the claim by `simpa` alone is rejected.
credence is your honest chance that the lemma is true. A false lemma wastes
everything built on it, so test each one numerically before you commit to it.
{sketches}
"""

GUESS = """The question asks for a value. ANSWER stands for it in:

    {statement}

Propose the value you think is most likely right, as a Lean term. Already
proposed: {tried}. Use python3 to compute small cases and look for the pattern.
Write answer.json:

    {{"answer": "<Lean term>", "credence": 0.3, "why": "one paragraph"}}

"""


def why(tree, k):
    """The chain of sketches from the root down to this claim."""
    lines, seen = [], set()
    while k not in tree.roots and k not in seen:
        seen.add(k)
        s = next((s for s, sk in tree.sketches.items() if k in sk["lemmas"]), None)
        if s is None:
            break
        sk = tree.sketches[s]
        parent = tree.claims[sk["claim"]]
        lines.append(f"It is a lemma in a plan for `{parent['statement']}`:\n{sk['informal'].strip()}\n")
        k = parent["key"]
    return "\n".join(lines)


def library(tree, limit=40):
    if not tree.library:
        return ""
    rows = [f"    {e['name']} : {e['statement']}" for e in tree.library[-limit:]]
    return "Proved lemmas you may cite by name (the judge adds them to your file):\n\n" + "\n".join(rows) + "\n"


def goal(tree, kind, k, check):
    c = tree.claims[k] if k else None
    p = tree.problem
    shared = SHARED.format(
        root=p["statement"], preamble=p.get("preamble", "").replace("\n", "\n    "),
        why=why(tree, k) if k else "", library=library(tree), hints=p.get("hints", ""),
    )
    if kind == "guess":
        tried = ", ".join(f"`{tree.claims[r]['statement']}`" for r in tree.roots) or "nothing"
        head = GUESS.format(statement=p["statement"], tried=tried)
    elif kind == "decompose":
        done = [tree.sketches[s] for s in c["sketches"]]
        sketches = "".join(f"\nAn earlier sketch used: {'; '.join(sk['texts'])}. Find a different route." for sk in done)
        head = DECOMPOSE.format(statement=c["statement"], max_lemmas=tree.cfg["max_lemmas"], sketches=sketches)
    else:
        head = (PROVE if kind == "prove" else FALSIFY).format(statement=c["statement"])
    return head + shared + "\n" + GATE.format(check=check)
