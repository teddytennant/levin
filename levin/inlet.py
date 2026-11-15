"""levin's tasks, run on an inlet daemon through its CLI."""
import json
import os
import shutil
import subprocess
import tempfile


class Inlet:
    def __init__(self, bin="inlet", home=None):
        self.bin = bin
        self.home = os.path.expanduser(home or os.environ.get("INLET_HOME") or "~/.inlet")

    def cli(self, *args):
        out = subprocess.run([self.bin, "--home", self.home, *args], capture_output=True, text=True)
        if out.returncode:
            raise RuntimeError(f"inlet {args[0]}: {(out.stderr or out.stdout).strip()}")
        return out.stdout

    def submit(self, worker, goal, verify, files, tokens, retries, memory_mb=None):
        """Queue a task whose workdir starts with `files`. Returns its id."""
        seed = tempfile.mkdtemp(prefix="levin-seed-")
        try:
            for name, text in files.items():
                with open(os.path.join(seed, name), "w") as f:
                    f.write(text)
            args = ["add", "-w", worker, "-g", goal, "--verify", verify, "--tokens", str(tokens),
                    "--retries", str(retries), "--seed", seed, "-t", "levin"]
            if memory_mb:
                args += ["--memory-mb", str(memory_mb)]
            out = self.cli(*args)
        finally:
            shutil.rmtree(seed)
        return out.split()[-1]

    def chains(self):
        tasks = {t["id"]: t for t in json.loads(self.cli("get", "tasks", "--json"))}
        return tasks, {t["retry_of"]: t["id"] for t in tasks.values() if t.get("retry_of")}

    def kill(self, id):
        """Stop a task, or the retry of it that is running now."""
        _, retry = self.chains()
        while id in retry:
            id = retry[id]
        try:
            self.cli("kill", id)
        except RuntimeError:
            pass

    def settled(self, ids):
        """For each of `ids` whose last retry has finished:
        {id: {"ok", "reason", "used", "last"}}. `used` counts every retry."""
        tasks, retry = self.chains()
        out = {}
        for id in ids:
            if id not in tasks:
                continue
            chain = [id]
            while chain[-1] in retry:
                chain.append(retry[chain[-1]])
            last = tasks[chain[-1]]
            if last["state"] in ("done", "failed", "killed"):
                out[id] = {"ok": last["state"] == "done", "reason": last.get("reason"), "last": last["id"],
                           "used": sum(tasks[x].get("used", 0) for x in chain)}
        return out

    def read(self, id, name):
        try:
            with open(os.path.join(self.home, "work", id, name)) as f:
                return f.read()
        except OSError:
            return None
