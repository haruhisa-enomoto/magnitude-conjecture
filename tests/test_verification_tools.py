import unittest

from scripts.audit_axioms import ALLOWED, parse_report
from scripts.build_lean_serial import lake_selector, pending_targets


class LakeFrontierTests(unittest.TestCase):
    def test_real_mixed_frontier(self):
        output = """error: target is out-of-date and needs to be rebuilt
Some required targets logged failures:
- leansqlite/sqlite.o
- leansqlite.static:shared
- MD4Lean:shared
- DocGen4.Process.Base
- Main:c.o
- «doc-gen4»:exe
"""
        self.assertEqual([lake_selector(t) for t in pending_targets(output)], [
            "leansqlite/sqlite.o", "leansqlite:shared", "MD4Lean:shared",
            "+DocGen4.Process.Base", "+Main:c.o", "doc-gen4:exe"])

    def test_compiler_errors_do_not_become_a_frontier(self):
        with self.assertRaises(RuntimeError):
            pending_targets("error: unknown module\nSome required targets logged failures:\n- A\n")

    def test_unrecognized_targets_stop_the_build(self):
        with self.assertRaises(RuntimeError):
            pending_targets("error: target is out-of-date and needs to be rebuilt\n"
                            "Some required targets logged failures:\n- A --other-option\n")


class AxiomReportTests(unittest.TestCase):
    def test_apostrophes_in_lean_names(self):
        reports = parse_report(
            "'MagnitudeConjecture.CoveringHom.shiftHomComp'_assoc' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
            "'lemma''_name' does not depend on any axioms\n")
        self.assertEqual(reports, {
            "MagnitudeConjecture.CoveringHom.shiftHomComp'_assoc": ALLOWED,
            "lemma''_name": set(),
        })

    def test_multiline_and_axiom_free_reports(self):
        reports = parse_report("'A' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
                               "'B' does not depend on any axioms\n")
        self.assertEqual(reports, {"A": ALLOWED, "B": set()})

    def test_unexpected_axioms_remain_visible(self):
        reports = parse_report("'A' depends on axioms: [propext, sorryAx, MyAxiom]\n")
        self.assertEqual(reports["A"] - ALLOWED, {"sorryAx", "MyAxiom"})


if __name__ == "__main__":
    unittest.main()
