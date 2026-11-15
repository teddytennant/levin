import os
import shutil
import subprocess
import unittest

from levin import check

LEAN = os.environ.get("LEVIN_LEAN") or shutil.which("lean")


def works(lean):
    try:
        return subprocess.run([lean, "--version"], capture_output=True).returncode == 0
    except (TypeError, OSError):
        return False


def claim(kind, statement, **more):
    checker = os.path.join(os.path.dirname(os.path.realpath(LEAN or "")), "leanchecker")
    return {"kind": kind, "statement": statement, "preamble": "", "lean": [LEAN], "leanchecker": [checker], **more}


@unittest.skipUnless(works(LEAN), "set LEVIN_LEAN to a working lean binary")
class GateTest(unittest.TestCase):
    def test_proof(self):
        self.assertIsNone(check.check(claim("prove", "∀ n : Nat, n + 0 = n"), "fun n => rfl"))

    def test_sorry(self):
        self.assertEqual(check.check(claim("prove", "1 = 2"), "by sorry"), "the proof uses sorry")

    def test_native_decide(self):
        why = check.check(claim("prove", "(10 : Nat) < 20"), "by native_decide")
        self.assertIn("outside propext", why)

    def test_commands_are_refused_before_lean_runs(self):
        for body in ("by decide\n#eval 1", "by\n  run_tac pure ()", "by decide\naxiom x : False",
                     "by\n  set_option debug.skipKernelTC true in decide"):
            self.assertIn("not allowed", check.check(claim("prove", "1 = 1"), body))

    def test_code_hidden_behind_a_string_is_refused(self):
        body = ('by\n  have _h : String := "--"; run_tac do let n := (← Lean.Elab.Term.getDeclName?).get! ++ `bad; '
                'Lean.withOptions (fun o => o.setBool `debug.skipKernelTC true) (Lean.addDecl (.thmDecl { name := n, '
                'levelParams := [], type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat) (Lean.mkNatLit 1) '
                '(Lean.mkNatLit 2), value := Lean.mkConst ``True.intro })); Lean.Elab.Tactic.closeMainGoal `x (Lean.mkConst n)')
        self.assertEqual(check.check(claim("prove", "(1:Nat) = 2", preamble="import Lean"), body), "`\"` is not allowed here")

    def test_wrong_proof(self):
        self.assertIn("decide", check.check(claim("prove", "2 + 2 = 5"), "by decide"))

    def test_sketch(self):
        c = claim("sketch", "∀ a b : Nat, a + b = b + a ∧ a * b = b * a")
        s = {"lemmas": [{"statement": "∀ a b : Nat, a + b = b + a"}, "∀ a b : Nat, a * b = b * a"],
             "body": "fun a b => ⟨h1 a b, h2 a b⟩"}
        self.assertIsNone(check.check(c, s))

    def test_sketch_lemma_must_be_a_prop(self):
        c = claim("sketch", "1 = 1")
        self.assertIn("Prop", check.check(c, {"lemmas": ["Nat"], "body": "rfl"}))
        self.assertIn("Prop", check.check(claim("sketch", "∀ n : Nat, n * 1 = n"), {"lemmas": ["Nat"], "body": "sorry"}))

    def test_sketch_must_make_progress(self):
        c = claim("sketch", "∀ n : Nat, n + 0 = n")
        why = check.check(c, {"lemmas": ["∀ m : Nat, m + 0 = m", "1 = 1"], "body": "h1"})
        self.assertEqual(why, "lemma 1 gives the claim by simp alone, so the sketch makes no progress")

    def test_lemma_statement_cannot_run_tactics(self):
        c = claim("sketch", "1 = 1")
        self.assertEqual(check.check(c, {"lemmas": ["(by exact True)"], "body": "rfl"}),
                         "lemma `(by exact True)`: a statement cannot contain `by`")

    def test_library_is_cited(self):
        lib = [{"name": "L_000000000001", "statement": "2 + 2 = 4", "deps": [],
                "text": "theorem L_000000000001 : 2 + 2 = 4 := rfl"}]
        c = claim("prove", "2 + 2 = 4 ∧ True", library=lib)
        self.assertIsNone(check.check(c, "⟨L_000000000001, trivial⟩"))

    def test_answer_must_fit(self):
        self.assertIsNone(check.check(claim("prop", "2 + 2 = ANSWER"), {"answer": "4"}))
        self.assertIsNotNone(check.check(claim("prop", "(2 : Nat) + 2 = ANSWER"), {"answer": "-4"}))

    def test_fractions_only_when_asked_for(self):
        self.assertIn("must be an integer", check.check(claim("prop", "2 + 2 = ANSWER"), {"answer": "8/2"}))

    def test_the_proved_type_must_be_the_statement(self):
        c = claim("prove", "True")
        self.assertIsNone(check.gate(c, check.proof_file(c, "True", "trivial", "levin_t"), "levin_t", "True"))
        why = check.gate(c, check.proof_file(c, "True", "trivial", "levin_t"), "levin_t", "1 = 2")
        self.assertIn("mismatch", why)

    def test_preamble_namespace_and_notation(self):
        preamble = "namespace Foo\nlocal notation \"two\" => (2 : Nat)\nvariable (k : Nat)"
        self.assertIsNone(check.check(claim("prove", "two + two = 4", preamble=preamble), "rfl"))

    def test_answer_cannot_splice(self):
        why = check.check(claim("prop", "ANSWER * 0 = 1"), {"answer": "0) * 0 = 1 ∨ True ∨ ((0 : Nat)"})
        self.assertIn("must be an integer", why)

    def test_certificate_is_replayed(self):
        cert = ("set_option autoImplicit false\n\ntheorem L_000000000001 : 2 + 2 = 4 := rfl\n\n"
                "theorem levin_root : 2 + 2 = 4 := L_000000000001\n")
        self.assertIsNone(check.check(claim("cert", "2 + 2 = 4"), cert))


if __name__ == "__main__":
    unittest.main()
