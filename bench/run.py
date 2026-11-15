#!/usr/bin/env python3
"""Matched-budget comparison of search arms on a list of statements.

    python3 bench/run.py <out_dir> <base.json> <statements.txt> [seconds]

base.json is a problem file without "statement"; each line of
statements.txt is one statement. Every arm gets the same budget. Prints one
row per statement: for each arm, whether it settled the statement and the
tokens spent when it stopped.
"""
import json
import os
import subprocess
import sys
import time

ARMS = {
    "best-of-N": {"max_sketches": 0, "falsify": False, "notes": False},
    "levin": {},
    "round-robin": {"planner": "round_robin"},
}


def settled(dir):
    solved, spent = False, 0
    with open(os.path.join(dir, "events.jsonl")) as f:
        for line in f:
            e = json.loads(line)
            spent += e.get("used", 0) if e["ev"] == "settle" else 0
            solved = solved or (e["ev"] == "settle" and e["kind"] == "cert" and e.get("outcome") == "accepted")
    return solved, spent


def main(out, base, statements, seconds=3600):
    with open(base) as f:
        base = json.load(f)
    with open(statements) as f:
        statements = [line.strip() for line in f if line.strip()]
    runs = []
    for i, statement in enumerate(statements):
        for arm, more in ARMS.items():
            dir = os.path.join(out, f"{i}-{arm}")
            if not os.path.exists(dir):
                path = dir + ".json"
                os.makedirs(out, exist_ok=True)
                with open(path, "w") as f:
                    json.dump({**base, **more, "statement": statement}, f)
                subprocess.run([sys.executable, "-m", "levin", "init", path, dir], check=True, capture_output=True)
            log = open(dir + ".log", "a")
            runs.append(subprocess.Popen([sys.executable, "-m", "levin", "run", dir], stdout=log, stderr=log))
    deadline = time.time() + float(seconds)
    while any(r.poll() is None for r in runs) and time.time() < deadline:
        time.sleep(10)
    for r in runs:
        if r.poll() is None:
            r.terminate()
    print("statement".ljust(48), *(arm.rjust(18) for arm in ARMS))
    for i, statement in enumerate(statements):
        cells = []
        for arm in ARMS:
            solved, spent = settled(os.path.join(out, f"{i}-{arm}"))
            cells.append(f"{'yes' if solved else 'no'} {spent // 1000}k".rjust(18))
        print(statement[:48].ljust(48), *cells)


if __name__ == "__main__":
    main(*sys.argv[1:])
