"""Regression tests for false-positive verification results."""
import unittest
import verify


class AuditTests(unittest.TestCase):
    def test_accepts_standard_axioms_and_axiom_free_proofs(self):
        output = "'a' depends on axioms: [propext, Classical.choice, Quot.sound]\n'b' does not depend on any axioms\n"
        self.assertEqual(set(verify.check_axioms(output, ['a', 'b'])), {'a', 'b'})

    def test_rejects_admitted_proof(self):
        with self.assertRaises(ValueError):
            verify.check_axioms("'a' depends on axioms: [sorryAx]\n", ['a'])

    def test_rejects_extra_assumption(self):
        with self.assertRaises(ValueError):
            verify.check_axioms("'a' depends on axioms: [Assume.main_theorem]\n", ['a'])

    def test_rejects_missing_declaration(self):
        with self.assertRaises(ValueError):
            verify.check_axioms("'a' does not depend on any axioms\n", ['a', 'b'])

    def test_rejects_duplicate_result(self):
        with self.assertRaises(ValueError):
            verify.check_axioms("'a' does not depend on any axioms\n" * 2, ['a'])

    def test_rejects_compiler_diagnostics(self):
        with self.assertRaises(ValueError):
            verify.check_axioms("'a' does not depend on any axioms\nerror: compilation failed\n", ['a'])


class InventoryTests(unittest.TestCase):
    def test_accepts_exact_compiled_inventory(self):
        rows = verify.check_inventory(
            '{"name":"a","kind":"theorem","axioms":["propext"]}\n', ['a'])
        self.assertEqual(rows[0]['name'], 'a')

    def test_rejects_unlisted_declaration(self):
        with self.assertRaises(ValueError):
            verify.check_inventory(
                '{"name":"hidden","kind":"definition","axioms":[]}\n', ['a'])

    def test_rejects_project_axiom(self):
        with self.assertRaises(ValueError):
            verify.check_inventory(
                '{"name":"a","kind":"axiom","axioms":[]}\n', ['a'])

    def test_rejects_disallowed_transitive_axiom(self):
        with self.assertRaises(ValueError):
            verify.check_inventory(
                '{"name":"a","kind":"theorem","axioms":["sorryAx"]}\n', ['a'])


if __name__ == '__main__':
    unittest.main()
