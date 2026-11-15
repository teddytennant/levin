import unittest
from math import prod

from levin.tree import Tree, key, negate


def sketch(*lemmas, body="h1"):
    return {"lemmas": [{"statement": x, "credence": 0.9} for x in lemmas], "body": body, "informal": ""}


class TreeTest(unittest.TestCase):
    def test_open_question_has_both_sides(self):
        t = Tree({"statement": "P", "truth": 0.7})
        p, n = (t.claims[r] for r in t.roots)
        self.assertEqual(n["statement"], "¬(P)")
        self.assertAlmostEqual(p["t"] + n["t"], 1.0)
        self.assertEqual({a[1] for a in t.actions()}, {"prove", "decompose"})

    def test_known_theorem_has_one_side(self):
        t = Tree({"statement": "P", "truth": 1.0})
        self.assertEqual(len(t.roots), 1)

    def test_failed_proof_moves_belief_to_the_other_side(self):
        t = Tree({"statement": "P"})
        p, n = (t.claims[r] for r in t.roots)
        before = t.p(p)
        t.fail("prove", p["key"])
        self.assertLess(p["t"], 0.5)
        self.assertAlmostEqual(n["t"], 1 - p["t"])
        self.assertLess(t.p(p), before)

    def test_the_likelier_side_is_split_first(self):
        t = Tree({"statement": "P"})
        t.fail("prove", t.roots[1])
        split = [k for _, kind, k in t.actions() if kind == "decompose"]
        self.assertEqual(split, t.roots)

    def test_new_lemmas_are_falsified_before_they_are_proved(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], sketch("A", "B"))
        kinds = {(kind, k) for _, kind, k in t.actions()}
        self.assertIn(("falsify", key("A")), kinds)
        self.assertNotIn(("prove", key("A")), kinds)
        t.fail("falsify", key("A"))
        self.assertGreater(t.claims[key("A")]["t"], 0.9)
        self.assertIn(("prove", key("A")), {(kind, k) for _, kind, k in t.actions()})

    def test_proving_every_lemma_closes_the_root(self):
        t = Tree({"statement": "P"})
        t.sketched(t.roots[0], sketch("A", "B", body="h1 h2"))
        t.proved(key("A"), "a")
        self.assertIsNone(t.solved())
        t.proved(key("B"), "b")
        self.assertEqual(t.solved(), t.roots[0])
        self.assertEqual(t.claims[t.roots[1]]["status"], "refuted")
        self.assertEqual(t.certificate(), "\n\nset_option autoImplicit false\n\n"
                         f"theorem L_{key('A')} : A := a\n\n"
                         f"theorem L_{key('B')} : B := b\n\n"
                         f"theorem R_{t.roots[0]}_0 (h1 : A) (h2 : B) : P := h1 h2\n\n"
                         f"theorem L_{t.roots[0]} : P := R_{t.roots[0]}_0 L_{key('A')} L_{key('B')}\n\n"
                         f"theorem levin_root : P := L_{t.roots[0]}\n")

    def test_a_sketch_of_proved_lemmas_closes_at_once(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], sketch("A"))
        t.proved(key("A"), "a")
        self.assertEqual(t.solved(), t.roots[0])

    def test_refuted_lemma_kills_its_sketch(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], sketch("A", "B"))
        before = t.chance()
        t.refuted(key("A"), "fun h => h")
        self.assertLess(t.chance(), before)
        self.assertEqual(t.library[0]["name"], f"L_{key(negate('A'))}")

    def test_refuting_a_root_proves_the_other_side(self):
        t = Tree({"statement": "P"})
        t.refuted(t.roots[0], "nope")
        self.assertEqual(t.solved(), t.roots[1])

    def test_dead_sketches_do_not_use_up_the_root(self):
        t = Tree({"statement": "P", "truth": 1.0, "max_sketches": 1})
        t.sketched(t.roots[0], sketch("A"))
        self.assertNotIn("decompose", [kind for _, kind, _ in t.actions()])
        t.refuted(key("A"), "a_false")
        self.assertIn("decompose", [kind for _, kind, _ in t.actions()])
        self.assertIn("`A`, which is false", t.claims[t.roots[0]]["notes"])

    def test_vetted_sketch_lifts_belief(self):
        t = Tree({"statement": "P", "truth": 0.2})
        t.sketched(t.roots[0], sketch("A", "B"))
        self.assertEqual(t.claims[t.roots[0]]["t"], 0.2)
        t.fail("falsify", key("A"))
        t.fail("falsify", key("B"))
        self.assertAlmostEqual(t.claims[t.roots[0]]["t"], 0.6 * 0.6)
        self.assertAlmostEqual(t.claims[t.roots[1]]["t"], 1 - 0.6 * 0.6)

    def test_disproving_not_p_proves_p(self):
        t = Tree({"statement": "P"})
        t.refuted(t.roots[1], "h")
        self.assertEqual(t.solved(), t.roots[0])
        self.assertIn(f"L_{t.roots[0]} : P := Classical.byContradiction L_", t.certificate())

    def test_a_late_second_proof_changes_nothing(self):
        t = Tree({"statement": "P"})
        t.proved(t.roots[0], "p")
        t.refuted(t.roots[1], "late")
        self.assertEqual([e["name"] for e in t.library], [f"L_{t.roots[0]}"])

    def test_confident_lemmas_cannot_move_the_root_alone(self):
        t = Tree({"statement": "P", "truth": 0.2, "lemma_truth": 0.6})
        t.sketched(t.roots[0], sketch("A", "B"))
        t.fail("falsify", key("A"))
        t.fail("falsify", key("B"))
        self.assertAlmostEqual(t.claims[t.roots[0]]["t"], 0.6 * 0.6)
        t.proved(key("A"), "a")
        self.assertAlmostEqual(t.claims[t.roots[0]]["t"], 0.6)
        t.fail("prove", t.roots[0])
        self.assertAlmostEqual(t.claims[t.roots[0]]["t"], 0.6)

    def test_cycles_are_refused(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], sketch("A"))
        self.assertFalse(t.sketched(key("A"), sketch("P")))
        self.assertEqual(t.claims[key("A")]["sketch_fails"], 1)

    def test_shared_lemma_is_one_claim(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], sketch("A", "B"))
        t.sketched(t.roots[0], sketch("A", "C"))
        self.assertEqual(len(t.claims), 4)
        t.proved(key("A"), "a")
        t.proved(key("C"), "c")
        self.assertEqual(t.solved(), t.roots[0])

    def test_gradient_matches_finite_difference(self):
        t = Tree({"statement": "P"})
        t.sketched(t.roots[0], sketch("A", "B"))
        t.sketched(key("A"), sketch("C", "B"))
        t.sketched(t.roots[1], sketch("D"))
        order = t.order()
        S = t.values(order)
        g, _ = t.grads(order, S)
        for k in (key("A"), key("B"), key("C"), key("D")):
            c, eps = t.claims[k], 1e-6
            c["t"] += eps
            up = total(t)
            c["t"] -= 2 * eps
            down = total(t)
            c["t"] += eps
            routes = prod(1 - t.sketch_value(s, S) for s in c["sketches"])
            self.assertAlmostEqual((up - down) / (2 * eps), g[k] * t.reach(c) * routes, places=6)

    def test_informal_sketch_waits_for_its_glue(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], {"lemmas": ["A"], "informal": "A gives P"})
        s = t.claims[t.roots[0]]["sketches"][0]
        t.proved(key("A"), "a")
        self.assertIsNone(t.solved())
        self.assertEqual(t.actions()[0][1:], ("formalize", s))
        before = t.chance()
        t.fail("formalize", s)
        self.assertLess(t.chance(), before)
        t.formalized(s, "h1")
        self.assertEqual(t.solved(), t.roots[0])
        self.assertIn(f"theorem R_{s} (h1 : A) : P := h1", t.certificate())

    def test_definitions_reach_the_certificate(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], {"lemmas": ["d_good 3"], "defs": ["def d_good (n : Nat) : Prop := n > 2"], "body": "h1"})
        t.proved(key("d_good 3"), "by decide")
        self.assertIn("def d_good (n : Nat) : Prop := n > 2\n\ntheorem L_", t.certificate())

    def test_search_keeps_the_best_and_stops_at_the_target(self):
        t = Tree({"statement": "P", "score": {"cmd": ["python3"], "target": 10}})
        side = t.roots[1]
        self.assertIn(("search", side), [a[1:] for a in t.actions()])
        t.searched(side, "x = 3", 3.0)
        t.searched(side, "x = 2", 2.0)
        self.assertEqual([b["score"] for b in t.claims[side]["best"]], [3.0, 2.0])
        self.assertEqual(t.claims[side]["search_fails"], 1)
        t.searched(side, "x = 10", 10.0)
        self.assertIn("x = 10", t.claims[side]["notes"])
        self.assertNotIn("search", [a[1] for a in t.actions()])

    def test_hopeless_glue_frees_the_claim(self):
        t = Tree({"statement": "P", "truth": 1.0, "max_sketches": 1})
        t.sketched(t.roots[0], {"lemmas": ["A"], "informal": ""})
        s = t.claims[t.roots[0]]["sketches"][0]
        self.assertNotIn("decompose", [a[1] for a in t.actions()])
        for _ in range(3):
            t.fail("formalize", s)
        self.assertIn("decompose", [a[1] for a in t.actions()])
        self.assertNotIn("formalize", [a[1] for a in t.actions()])

    def test_a_definition_name_means_one_thing(self):
        t = Tree({"statement": "P", "truth": 1.0})
        t.sketched(t.roots[0], {"lemmas": ["d_f = 1"], "defs": ["def d_f : Nat := 1"], "body": "h1"})
        self.assertFalse(t.sketched(t.roots[0], {"lemmas": ["d_f = 2"], "defs": ["def d_f : Nat := 2"], "body": "h1"}))
        self.assertTrue(t.sketched(t.roots[0], {"lemmas": ["d_f = 1 ∧ True"], "defs": ["def d_f : Nat := 1"], "body": "h1.1"}))
        self.assertEqual(len(t.defs), 1)

    def test_a_goal_without_a_statement_only_searches(self):
        t = Tree({"goal": "fewer Toffolis", "score": {"cmd": ["python3"], "target": 5}})
        self.assertEqual([a[1] for a in t.actions()], ["search"])
        t.searched(t.roots[0], "c", 5.0)
        self.assertEqual(t.actions(), [])

    def test_round_robin_ignores_the_scores(self):
        t = Tree({"statement": "P", "planner": "round_robin"})
        first = t.actions()[0]
        t.picked(first[1], first[2])
        self.assertNotEqual(t.actions()[0][1:], first[1:])

    def test_falsify_can_be_turned_off(self):
        t = Tree({"statement": "P", "truth": 1.0, "falsify": False})
        t.sketched(t.roots[0], sketch("A"))
        self.assertNotIn("falsify", [a[1] for a in t.actions()])

    def test_guesses_become_roots(self):
        t = Tree({"statement": "f 3 = ANSWER", "max_guesses": 2})
        self.assertEqual([a[1] for a in t.actions()], ["guess"])
        c = t.guessed("07", 0.4)
        self.assertEqual(c["statement"], "f 3 = (7)")
        self.assertFalse(c["falsified"])
        self.assertEqual(t.roots, [c["key"]])



def total(t):
    S = t.values(t.order())
    return sum(S[r] for r in t.roots)


if __name__ == "__main__":
    unittest.main()
