"""Tests of the file handling of framedit.py (standard library only):

    python3 -I tools/framedit/test_framedit.py

A Lean file with zero, one or several raw strings, nested delimiters, an
unclosed string, a repeated name, and the round trip of an edit."""
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import framedit  # noqa: E402

SEVERAL = '''import Foo
/-- first -/
def figsA : String := r#"
fig a = s <= t
"#

def other : Nat := 3

def figsB : String := r##"
-- a comment with "# in it
fig b = s R t
"##
'''


def source(text, name=None, ext='.lean'):
    d = tempfile.mkdtemp()
    p = os.path.join(d, 'F' + ext)
    with open(p, 'w', encoding='utf-8') as f:
        f.write(text)
    return framedit.Source(p, name)


class T(unittest.TestCase):
    def test_none(self):
        with self.assertRaises(ValueError):
            source('def x : Nat := 3\n').read()

    def test_figure_file(self):
        s = source('fig a = s <= t\n', ext='.fgd')
        _, before, text, after, kind, off = s.read()
        self.assertEqual((before, text, after, kind, off), ('', 'fig a = s <= t\n', '', 'figure file', 0))
        self.assertEqual(s.strings('x'), [])

    def test_several_first_by_default(self):
        s = source(SEVERAL)
        full, _, text, _, kind, off = s.read()
        self.assertEqual(text, '\nfig a = s <= t\n')
        self.assertEqual(kind, 'Lean string figsA')
        self.assertEqual(off, 2)
        self.assertEqual(s.strings(full), [{'name': 'figsA', 'line': 3}, {'name': 'figsB', 'line': 9}])

    def test_choose_and_nested(self):
        s = source(SEVERAL, 'figsB')
        _, _, text, after, _, _ = s.read()
        # `"#` inside an r##"…"## string does not end it
        self.assertEqual(text, '\n-- a comment with "# in it\nfig b = s R t\n')
        self.assertTrue(after.startswith('"##'))

    def test_unknown_name(self):
        with self.assertRaises(ValueError):
            source(SEVERAL, 'nope').read()

    def test_unclosed(self):
        with self.assertRaises(ValueError):
            source('def f : String := r#"\nfig a = s <= t\n').read()

    def test_repeated_name(self):
        with self.assertRaises(ValueError):
            source('def f : String := r#"x"#\ndef f : String := r#"y"#\n', 'f').read()

    def test_definition_inside_a_string_is_not_one(self):
        s = source('def f : String := r#"\n-- def g : String := r#"\n"#\n')
        full = s.read()[0]
        self.assertEqual([x['name'] for x in s.strings(full)], ['f'])

    def test_round_trip(self):
        s = source(SEVERAL, 'figsB')
        full, before, text, after, _, _ = s.read()
        self.assertEqual(before + text + after, full)


if __name__ == '__main__':
    unittest.main()
