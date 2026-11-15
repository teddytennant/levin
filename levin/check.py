#!/usr/bin/env python3
"""The Lean gate. Stdlib only, because it also runs alone inside a cell.

    python3 check.py claim.json

claim.json is written by levin and says what is being checked:

    kind       prove | sketch | prop | cert
    preamble   imports and opens
    statement  the Lean proposition (for prop, with ANSWER in it)
    negation   for prove, the statement's negation
    lean       command that runs Lean, e.g. ["lake", "env", "lean"]
    leanchecker  command that runs leanchecker
    lean_dir   where to run them
    library    proved lemmas a proof may cite: [{"name", "text", "deps"}]

The artifact sits beside it: proof.lean (the text after `:=`), or for prove
negation.lean (a proof of the negation instead), sketch.json, answer.json, or
cert.lean. Exit 0 means accepted.

What a worker wrote is compiled as a module, the module is replayed through
the kernel by leanchecker, and its axioms are read by a second Lean process
that only imports it, so nothing the worker's code printed is believed.
"""
import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import tempfile

AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

DENY = {
    "axiom", "axioms", "theorem", "lemma", "def", "example", "instance", "abbrev",
    "structure", "class", "inductive", "opaque", "partial", "unsafe", "mutual",
    "namespace", "section", "end", "import", "export", "universe", "variable",
    "attribute", "macro", "macro_rules", "syntax", "elab", "elab_rules",
    "declare_syntax_cat", "notation", "infix", "infixl", "infixr", "prefix",
    "postfix", "initialize", "builtin_initialize", "implemented_by", "extern",
    "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab", "local", "scoped",
}
OPTIONS = {"maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats"}
ANSWER = re.compile(r"-?[0-9]+(/[0-9]+)?")
LEMMA = re.compile(r"\bL_[0-9a-f]{12}\b")


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", " ", text)


def scan(text, statement=False):
    """Why this text cannot go into a proof, or None. String and name
    literals are refused outright: inside one, the rest of this scan would be
    reading the wrong thing."""
    for c in '"«»#':
        if c in text:
            return f"`{c}` is not allowed here"
    clean = strip_comments(text)
    for word in re.findall(r"[A-Za-z_][A-Za-z_0-9.']*", clean):
        if word in DENY or word.split(".")[0] in DENY:
            return f"`{word}` is not allowed here"
        if statement and word == "by":
            return "a statement cannot contain `by`"
    for opt in re.findall(r"set_option\s+(\S+)", clean):
        if statement or opt not in OPTIONS:
            return f"set_option {opt} is not allowed here"
    for a, b in ("()", "[]", "{}", "⟨⟩"):
        if clean.count(a) != clean.count(b):
            return "unbalanced brackets"
    return None


def normal(text):
    return " ".join(text.split())


def header(claim):
    return f"{claim['preamble']}\n\nset_option autoImplicit false\n\n"


def cited(library, texts):
    """Library entries the texts refer to, with what those need, in order."""
    by_name = {e["name"]: e for e in library}
    need, todo = set(), [n for t in texts for n in LEMMA.findall(t)]
    while todo:
        name = todo.pop()
        if name in by_name and name not in need:
            need.add(name)
            todo += by_name[name]["deps"]
    return "".join(e["text"] + "\n\n" for e in library if e["name"] in need)


def proof_file(claim, statement, body, name):
    lib = cited(claim.get("library", []), [body])
    return f"{header(claim)}{lib}theorem {name} : {statement} := {body}\n"


def sketch_file(claim, lemmas, body, name):
    """The reduction `lemmas -> statement`, a check that each lemma is a closed
    Prop, and a check that no lemma gives the statement by simp alone (a
    sketch has to make progress). Returns the text and, per lemma, the line of
    its progress check."""
    lib = cited(claim.get("library", []), [*lemmas, body])
    text = header(claim) + lib
    for lemma in lemmas:
        text += f"example : Prop := ({lemma})\n"
    lines = []
    for lemma in lemmas:
        lines.append(text.count("\n") + 2)
        text += f"\nexample : True := by\n  fail_if_success\n    have _ : ({lemma}) → ({claim['statement']}) := fun h => by simpa using h\n  trivial\n"
    binders = " ".join(f"(h{i + 1} : {lemma})" for i, lemma in enumerate(lemmas))
    text += f"\ntheorem {name} {binders} : {claim['statement']} := {body}\n"
    return text, lines


def run(cmd, claim, where, timeout):
    env = dict(os.environ)
    env["LEAN_PATH"] = where + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    if os.path.isabs(claim["lean"][0]):
        env["PATH"] = os.path.dirname(claim["lean"][0]) + ":" + env.get("PATH", "")
    try:
        return subprocess.run(cmd, cwd=claim.get("lean_dir") or None, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(cmd, 124, "", f"timed out after {timeout}s")


def messages(out):
    msgs = []
    for line in out.stdout.splitlines():
        try:
            msgs.append(json.loads(line))
        except ValueError:
            msgs.append({"severity": "error", "data": line})
    if out.returncode and not any(m.get("severity") == "error" for m in msgs):
        msgs.append({"severity": "error", "data": out.stderr.strip()[-2000:] or f"lean exited {out.returncode}"})
    return msgs


def build(claim, text, where):
    """Compile `text` as the module LevinCheck in `where`. Its messages."""
    path = os.path.join(where, "LevinCheck.lean")
    with open(path, "w") as f:
        f.write(text)
    out = run([*claim["lean"], "--json", f"--root={where}", "-o", os.path.join(where, "LevinCheck.olean"), path],
              claim, where, claim.get("timeout", 600))
    return messages(out)


def problems(msgs):
    errors = [m["data"] for m in msgs if m.get("severity") == "error"]
    if errors:
        return "\n\n".join(errors)[-4000:]
    if any(m.get("kind") == "hasSorry" or "declaration uses `sorry`" in m.get("data", "") for m in msgs):
        return "the proof uses sorry"
    return None


def scope(claim):
    """The preamble's opens and options, without its imports."""
    return "".join(line + "\n" for line in claim["preamble"].splitlines() if line.startswith(("open ", "set_option ")))


def audit(claim, where, name, expected, fresh=False):
    """Replay the built module through the kernel, then, in a process that
    only imports it, check `name` against levin's own statement and read its
    axioms. Nothing the worker's text did to its own scope reaches here."""
    replay = run([*claim.get("leanchecker", ["leanchecker"]), *(["--fresh"] if fresh else []), "LevinCheck"],
                 claim, where, claim.get("replay_timeout", 3600))
    if replay.returncode:
        return "leanchecker: " + (replay.stderr or replay.stdout).strip()[-2000:]
    path = os.path.join(where, "LevinAxioms.lean")
    with open(path, "w") as f:
        f.write(f"import LevinCheck\n\n{scope(claim)}set_option autoImplicit false\n\n"
                f"example : {expected} := {name}\n\n#print axioms {name}\n")
    msgs = messages(run([*claim["lean"], "--json", path], claim, where, claim.get("timeout", 600)))
    if why := problems(msgs):
        return why
    said = [m["data"] for m in msgs if m.get("data", "").startswith(f"'{name}' ")]
    if len(said) != 1:
        return "no axiom report for the theorem"
    if "does not depend on any axioms" in said[0]:
        return None
    extra = set(said[0].split("[", 1)[1].rstrip("]").replace(" ", "").split(",")) - AXIOMS
    return f"uses axioms outside propext, Classical.choice, Quot.sound: {', '.join(sorted(extra))}" if extra else None


def gate(claim, text, name, expected, fresh=False, judge=problems):
    where = tempfile.mkdtemp(prefix="levin-")
    try:
        return judge(build(claim, text, where)) or audit(claim, where, name, expected, fresh)
    finally:
        shutil.rmtree(where, ignore_errors=True)


def check_prove(claim, body, statement=None):
    body = body.strip()
    if not body:
        return "empty proof"
    if why := scan(body):
        return why
    name = f"levin_{secrets.token_hex(6)}"
    statement = statement or claim["statement"]
    return gate(claim, proof_file(claim, statement, body, name), name, statement)


def check_sketch(claim, sketch):
    lemmas = sketch.get("lemmas")
    if isinstance(lemmas, list):
        lemmas = [x.get("statement") if isinstance(x, dict) else x for x in lemmas]
    if not isinstance(lemmas, list) or not lemmas or not all(isinstance(x, str) and x.strip() for x in lemmas):
        return "lemmas must be a non-empty list of statements"
    top = claim.get("max_lemmas", 4)
    if len(lemmas) > top:
        return f"at most {top} lemmas"
    body = str(sketch.get("body", "")).strip()
    if not body:
        return "empty body"
    own = normal(claim["statement"])
    if any(normal(x) == own for x in lemmas):
        return "a lemma restates the claim"
    for lemma in lemmas:
        if why := scan(lemma, statement=True):
            return f"lemma `{normal(lemma)[:80]}`: {why}"
    if why := scan(body):
        return why
    name = f"levin_{secrets.token_hex(6)}"
    text, lines = sketch_file(claim, lemmas, body, name)

    def judge(msgs):
        stuck = [m for m in msgs if "expected to fail" in m.get("data", "")]
        if stuck and (why := problems([m for m in msgs if m not in stuck])):
            return why
        for i, line in enumerate(lines):
            if any(line <= m.get("pos", {}).get("line", 0) <= line + 3 for m in stuck):
                return f"lemma {i + 1} gives the claim by simp alone, so the sketch makes no progress"
        return problems(msgs)

    expected = " → ".join(f"({x})" for x in [*lemmas, claim["statement"]])
    return gate(claim, text, name, expected, judge=judge)


def check_prop(claim, answer):
    """A guessed value is a numeral or a fraction of numerals. Anything richer
    can restate the question (`sInf {n | P n}`) or splice into it."""
    term = str(answer.get("answer", "")).strip()
    fractions = claim.get("answer_type") in ("ℚ", "ℝ", "Rat", "Real")
    if not ANSWER.fullmatch(term) or ("/" in term and not fractions):
        return "an answer must be an integer" + (" or a fraction of integers, like 22/7" if fractions else "")
    statement = claim["statement"].replace("ANSWER", f"({term})")
    name = f"levin_{secrets.token_hex(6)}"
    return gate(claim, f"{header(claim)}theorem {name} : True := by\n  have _ : Prop := ({statement})\n  trivial\n", name, "True")


def check_cert(claim, text):
    return gate(claim, text, "levin_root", claim["statement"], fresh=claim.get("fresh", False))


KINDS = {"prove": ("proof.lean", check_prove), "sketch": ("sketch.json", check_sketch),
         "prop": ("answer.json", check_prop), "cert": ("cert.lean", check_cert)}


def check(claim, artifact):
    """None when the artifact is accepted, else the reason."""
    return KINDS[claim["kind"]][1](claim, artifact)


def main(argv):
    path = os.path.abspath(argv[1] if len(argv) > 1 else "claim.json")
    where = os.path.dirname(path)
    with open(path) as f:
        claim = json.load(f)
    name = KINDS[claim["kind"]][0]
    if claim["kind"] == "prove" and not os.path.exists(os.path.join(where, name)) and claim.get("negation"):
        name = "negation.lean"
    try:
        with open(os.path.join(where, name)) as f:
            artifact = json.load(f) if name.endswith(".json") else f.read()
    except (OSError, ValueError) as e:
        print(f"no artifact: {e}")
        return 1
    if claim["kind"] in ("sketch", "prop") and not isinstance(artifact, dict):
        print("the artifact must be a JSON object")
        return 1
    if name == "negation.lean":
        why = check_prove(claim, artifact, claim["negation"])
    else:
        why = check(claim, artifact)
    print("accepted" if why is None else why)
    return 0 if why is None else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
