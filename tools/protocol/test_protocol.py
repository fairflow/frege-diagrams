#!/usr/bin/env python3
"""Contract H3 of docs/design/NEXT-STAGE.md: every request the clients send,
and every reply of `framediag --serve`, matches docs/protocol/serve.schema.json.

Starts the server, sends a corpus covering every op, every edit kind and the
error cases, and checks each request against the request schema and each reply
against the reply schema of its op (or the error schema, where an error is
expected).  Needs `lake build framediag` and `pip install jsonschema==4.23.0`.

    python3 tools/protocol/test_protocol.py
"""
import json
import os
import subprocess
import sys

import jsonschema

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
SCHEMA = json.load(open(os.path.join(ROOT, "docs", "protocol", "serve.schema.json"), encoding="utf-8"))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "framediag")


def validator(pointer):
    """A validator for the subschema at `pointer` of the schema file."""
    s = dict(SCHEMA)
    s["$ref"] = pointer
    jsonschema.Draft202012Validator.check_schema(s)
    return jsonschema.Draft202012Validator(s)


REQUEST = validator("#/request")
ERROR = validator("#/$defs/error")
REPLY = {op: validator(f"#/replies/{op}") for op in SCHEMA["replies"]}

TEXT = """default dash <= ". "
fig one [size (200,120), s@(20,60), t@(180,60) label (4,-12), edge s>t bend 10,
    namedy t 2, notch t up, dash t "-- ", text (100,110) grey 10 middle "caption"] =
  all t. if s <= t then (t R t & ex u. t <=° u)
fig two [views B, judgement definition] = "D" {all x. s R x}
fig three [dash zz "- "] = all t. s <= t
fig four [views A, loop s 45] = s R s
"""

EDITS = [
    {"kind": "node", "name": "s", "panel": 1, "x": 30, "y": 50, "label": [0, -10]},
    {"kind": "node", "name": "t", "x": 150, "y": 50, "label": None},
    {"kind": "unnode", "name": "t", "panel": 1},
    {"kind": "edge", "src": "s", "tgt": "t", "occ": 1, "panel": 1, "bend": -20, "side": "+", "at": 50},
    {"kind": "edge", "src": "s", "tgt": "t", "bend": None, "side": None, "at": None},
    {"kind": "size", "w": 260, "h": 140},
    {"kind": "resize", "w": 400, "h": 240, "from": [200, 120]},
    {"kind": "resize", "w": 300, "h": 200, "from": None},
    {"kind": "namedy", "v": 3},
    {"kind": "namedy", "v": None},
    {"kind": "namedy", "name": "t", "v": -1},
    {"kind": "judgement", "v": "content"},
    {"kind": "stroke", "path": "b/0", "v": 12},
    {"kind": "gap", "path": "b/0/1", "v": 8},
    {"kind": "undash", "i": 0},
    {"kind": "loop", "name": "t", "panel": 1, "angle": 90},
    {"kind": "route", "name": "t", "polys": [[[0, 0], [0, -20], [80, -20]]]},
    {"kind": "route", "name": "t", "polys": None},
    {"kind": "notch", "name": "t", "dir": "down"},
    {"kind": "notch", "name": "t", "dir": None},
]

# (request, error expected)
CASES = [({"op": "parse", "text": TEXT, "id": 1}, False)]
for fig in ["one", "two", "three", "four"]:
    CASES += [
        ({"op": "render", "text": TEXT, "fig": fig}, False),
        ({"op": "render", "text": TEXT, "fig": fig, "only": "b",
          "opts": {"links": True, "hideBound": False, "nameDy": 1.5, "spacing": 1.2, "style": "classic"}}, False),
        ({"op": "body", "text": TEXT, "fig": fig}, False),
        ({"op": "lint", "text": TEXT, "fig": fig}, False),
        ({"op": "check", "text": TEXT, "fig": fig, "opts": {"links": True}}, False),
        ({"op": "block", "text": TEXT, "fig": fig, "path": "b"}, False),
    ]
CASES += [({"op": "edit", "text": TEXT, "fig": "one", "edit": e}, False) for e in EDITS]
CASES += [
    ({"op": "block", "text": TEXT, "fig": "one", "path": "b/7/7"}, True),   # no such block
    ({"op": "render", "text": TEXT, "fig": "nine"}, True),                 # no such figure
    ({"op": "parse", "text": "fig = "}, True),                             # does not parse
    ({"op": "edit", "text": TEXT, "fig": "three", "edit": {"kind": "undash", "i": 5}}, False),  # nothing to remove
]
# requests outside the schema: the server must still answer with an error
RAW = [
    ('{"op": "frobnicate", "text": ""}', True),
    ("not json", True),
    ('{"op": "render", "text": "fig a = s <= t"}', True),                  # no fig
]


def main():
    srv = subprocess.Popen([EXE, "--serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8")
    fails = []

    def ask(line):
        srv.stdin.write(line + "\n")
        srv.stdin.flush()
        return json.loads(srv.stdout.readline())

    def check(v, x, what):
        errs = sorted(v.iter_errors(x), key=lambda e: e.path)
        if errs:
            fails.append(f"{what}: {errs[0].message} at {list(errs[0].path)}")

    lint_fixes = 0
    for req, want_err in CASES:
        what = f"{req['op']} {req.get('fig', '')} {json.dumps(req.get('edit', ''))}".strip()
        check(REQUEST, req, f"request {what}")
        rep = ask(json.dumps(req))
        if want_err:
            if rep.get("ok") is not False:
                fails.append(f"{what}: expected an error, got {str(rep)[:120]}")
            check(ERROR, rep, f"error reply {what}")
            continue
        if rep.get("ok") is not True:
            fails.append(f"{what}: unexpected error {rep.get('error')}")
            continue
        check(REPLY[req["op"]], rep, f"reply {what}")
        if "id" in req and rep.get("id") != req["id"]:
            fails.append(f"{what}: id not echoed")
        if req["op"] == "lint":
            for it in rep["items"]:
                if it["fix"] is not None:
                    lint_fixes += 1
                    # a fix is an edit the server accepts
                    fr = {"op": "edit", "text": TEXT, "fig": req["fig"], "edit": it["fix"]}
                    check(REQUEST, fr, f"fix request {what}")
                    frep = ask(json.dumps(fr))
                    if frep.get("ok") is not True:
                        fails.append(f"fix of {what} refused: {frep.get('error')}")
    for line, _ in RAW:
        rep = ask(line)
        if rep.get("ok") is not False:
            fails.append(f"raw {line!r}: expected an error")
        check(ERROR, rep, f"error reply to {line!r}")
    srv.stdin.close()
    srv.wait(timeout=30)

    if lint_fixes == 0:
        fails.append("the corpus produced no lint fix, so fixes were not checked")
    n = len(CASES) + len(RAW)
    if fails:
        print("\n".join(fails))
        print(f"protocol: {len(fails)} failure(s) in {n} requests")
        sys.exit(1)
    print(f"protocol: {n} requests and replies match docs/protocol/serve.schema.json ({lint_fixes} lint fixes applied)")


if __name__ == "__main__":
    main()
