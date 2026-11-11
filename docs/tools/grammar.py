#!/usr/bin/env python3
"""The grammar of the figure language, as data: the one source of the EBNF in
docs/LANGUAGE.md and of the syntax (railroad) diagrams in docs/diagrams/.

    python3 docs/tools/grammar.py --ebnf               print the EBNF
    python3 docs/tools/grammar.py --check FILE         FILE's EBNF block equals the printed one
    python3 docs/tools/grammar.py --examples FILE OUT  write FILE's ```fgd blocks to OUT
    python3 docs/tools/grammar.py --svg DIR            one SVG per rule (needs: pip install railroad-diagrams)

The grammar follows the parser in FregeDiagrams/Syntax.lean; CI checks that
every example of docs/LANGUAGE.md parses (`framediag --fig`), and that the
EBNF in the document is this one.  Notation: W3C EBNF, as in the XML
specification: `::=`, `|`, `?`, `*`, `+`, quoted terminals, `[...]` and
`[^...]` character classes.
"""
import os
import re
import sys


class T:      # terminal
    def __init__(self, s): self.s = s
class N:      # nonterminal
    def __init__(self, s): self.s = s
class C:      # character class or other lexical item, printed as is
    def __init__(self, s): self.s = s
class Seq:
    def __init__(self, *xs): self.xs = xs
class Alt:
    def __init__(self, *xs): self.xs = xs
class Opt:
    def __init__(self, x): self.x = x
class Star:
    def __init__(self, x): self.x = x
class Plus:
    def __init__(self, x): self.x = x


def S(*xs):
    return xs[0] if len(xs) == 1 else Seq(*xs)


# (section, [(rule, expression)])
GRAMMAR = [
    ("Files and figures", [
        ("file", Star(N("figure"))),
        ("figure", Seq(T("fig"), N("name"), Opt(N("hints")), T("="), N("form"))),
    ]),
    ("Formulas", [
        ("form", Alt(
            Seq(T("all"), N("name"), T("."), N("form")),
            Seq(T("ex"), N("name"), T("."), N("form")),
            Seq(T("not"), N("form")),
            Seq(T("if"), N("form"), Star(Seq(T(","), N("form"))), T("then"), N("form")),
            Seq(T("("), N("form"), Opt(Alt(Plus(Seq(T("&"), N("form"))),
                                           Plus(Seq(T("|"), N("form"))))), T(")")),
            Seq(N("string"), Opt(Seq(T("{"), N("form"), T("}")))),
            N("chain"))),
        ("chain", Seq(N("state"), Star(Seq(N("relation"), N("state"))))),
        ("state", Seq(N("name"), Opt(T("°")))),
        ("relation", Seq(N("base"), Star(Seq(T(";"), N("base"))))),
        ("base", Alt(Seq(T("<="), Opt(T("°"))), Seq(T("R"), Opt(T("°"))), T("~>"), T("="), T("!="),
                     N("labelled"))),
    ]),
    ("Hints", [
        ("hints", Seq(T("["), Opt(Seq(N("hint"), Star(Seq(T(","), N("hint"))))), T("]"))),
        ("hint", Alt(N("size-hint"), N("views-hint"), N("position-hint"), N("edge-hint"),
                     N("loop-hint"), N("namedy-hint"), N("notch-hint"), N("text-hint"))),
        ("size-hint", Seq(T("size"), N("pair"))),
        ("views-hint", Seq(T("views"), Alt(T("A"), T("B")))),
        ("position-hint", Seq(N("key"), T("@"), N("pair"), Opt(Seq(T("label"), N("pair"))))),
        ("edge-hint", Seq(T("edge"), N("name"), T(">"), N("name"), Opt(Seq(T("#"), N("int"))),
                          Opt(Seq(T("/"), N("int"))), Star(N("edge-option")))),
        ("edge-option", Alt(Seq(T("bend"), N("int")), Seq(T("side"), Alt(T("+"), T("-"))),
                            Seq(T("at"), N("decimal")))),
        ("loop-hint", Seq(T("loop"), N("key"), N("int"))),
        ("namedy-hint", Seq(T("namedy"), N("int"))),
        ("notch-hint", Seq(T("notch"), N("name"), Alt(T("up"), T("down")))),
        ("text-hint", Seq(T("text"), N("pair"), Star(N("text-option")), N("string"))),
        ("text-option", Alt(T("black"), T("red"), T("grey"), N("int"), T("middle"), T("italic"))),
        ("key", Seq(N("name"), Opt(Seq(T("/"), N("int"))))),
        ("pair", Seq(T("("), N("int"), T(","), N("int"), T(")"))),
    ]),
    ("Tokens", [
        ("name", Seq(N("letter"), Star(Alt(N("letter"), N("digit"), T("'"), T("′"), N("subscript"))))),
        ("letter", Alt(C("[a-zA-Z]"), C("[Α-Ω]"), C("[α-ω]"), T("_"))),
        ("digit", C("[0-9]")),
        ("subscript", C("[₀-₉]")),
        ("int", Seq(Opt(T("-")), Plus(N("digit")))),
        ("decimal", Seq(Plus(N("digit")), Opt(Seq(T("."), N("digit"), Opt(N("digit")))))),
        ("string", Seq(C("'\"'"), Star(C('[^"]')), C("'\"'"))),
        ("labelled", Seq(T("-["), Star(C("[^\\]]")), Alt(T("]-"), T("]->")))),
    ]),
]


def ebnf(e, prec=0):
    """prec: 0 top, 1 inside a sequence, 2 under a postfix operator."""
    if isinstance(e, T):
        q = "'" if '"' in e.s else '"'
        return q + e.s + q
    if isinstance(e, (N, C)):
        return e.s
    if isinstance(e, Seq):
        s = " ".join(ebnf(x, 1) for x in e.xs)
        return f"( {s} )" if prec >= 2 else s
    if isinstance(e, Alt):
        s = " | ".join(ebnf(x, 1) for x in e.xs)
        return f"( {s} )" if prec >= 1 else s
    op = {Opt: "?", Star: "*", Plus: "+"}[type(e)]
    return ebnf(e.x, 2) + op


def ebnf_text():
    lines = []
    width = max(len(r) for _, rules in GRAMMAR for r, _ in rules)
    for section, rules in GRAMMAR:
        lines.append(f"/* {section} */")
        for r, e in rules:
            if isinstance(e, Alt) and len(e.xs) > 3:
                alts = [ebnf(x, 1) for x in e.xs]
                lines.append(f"{r.ljust(width)} ::= {alts[0]}")
                lines += [f"{' ' * width}   | {a}" for a in alts[1:]]
            else:
                lines.append(f"{r.ljust(width)} ::= {ebnf(e)}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


BEGIN, END = "<!-- ebnf:begin (generated by docs/tools/grammar.py; do not edit) -->", "<!-- ebnf:end -->"


def block_of(doc):
    m = re.search(re.escape(BEGIN) + r"\n```ebnf\n(.*?)```\n" + re.escape(END), doc, re.S)
    return m.group(1) if m else None


CSS = """
svg.railroad-diagram { background-color: #ffffff; }
svg.railroad-diagram path { stroke-width: 1.4; stroke: #1d2430; fill: none; }
svg.railroad-diagram text { font: 13px ui-monospace, Menlo, Consolas, monospace; text-anchor: middle; fill: #1d2430; }
svg.railroad-diagram text.label { text-anchor: start; }
svg.railroad-diagram rect { stroke-width: 1.4; stroke: #1d2430; fill: #eef2f8; }
svg.railroad-diagram g.non-terminal rect { fill: #ffffff; }
svg.railroad-diagram rect.bg { fill: #ffffff; stroke: none; }
svg.railroad-diagram rect.group-box { stroke: #888; stroke-dasharray: 10 5; fill: none; }
"""


def svgs(outdir):
    import railroad as rr

    def conv(e):
        if isinstance(e, T):
            return rr.Terminal(e.s)
        if isinstance(e, N):
            return rr.NonTerminal(e.s, href=f"{e.s}.svg")
        if isinstance(e, C):
            return rr.Terminal(e.s)
        if isinstance(e, Seq):
            return rr.Sequence(*[conv(x) for x in e.xs])
        if isinstance(e, Alt):
            return rr.Choice(0, *[conv(x) for x in e.xs])
        if isinstance(e, Opt):
            return rr.Optional(conv(e.x))
        if isinstance(e, Star):
            return rr.ZeroOrMore(conv(e.x))
        return rr.OneOrMore(conv(e.x))

    os.makedirs(outdir, exist_ok=True)
    for _, rules in GRAMMAR:
        for r, e in rules:
            d = rr.Diagram(conv(e))
            parts = []
            d.writeStandalone(parts.append, css=CSS)
            svg = "".join(parts)
            # an opaque background, so that the diagrams read in dark mode too
            svg = re.sub(r"(<svg[^>]*>)", r'\1<rect class="bg" width="100%" height="100%"/>', svg, count=1)
            with open(os.path.join(outdir, f"{r}.svg"), "w", encoding="utf-8") as f:
                f.write(svg)


def main(a):
    if a[:1] == ["--ebnf"]:
        sys.stdout.write(ebnf_text())
    elif a[:1] == ["--check"] and len(a) == 2:
        got = block_of(open(a[1], encoding="utf-8").read())
        if got != ebnf_text():
            sys.exit(f"{a[1]}: the EBNF block differs from docs/tools/grammar.py --ebnf; regenerate it")
        print(f"{a[1]}: EBNF block up to date")
    elif a[:1] == ["--examples"] and len(a) == 3:
        doc = open(a[1], encoding="utf-8").read()
        blocks = re.findall(r"```fgd\n(.*?)```", doc, re.S)
        with open(a[2], "w", encoding="utf-8") as f:
            f.write("\n".join(blocks))
        print(f"{len(blocks)} example blocks -> {a[2]}")
    elif a[:1] == ["--svg"] and len(a) == 2:
        svgs(a[1])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
