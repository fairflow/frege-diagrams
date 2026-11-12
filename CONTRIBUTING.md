# Contributing

## Documentation moves with the code

**Any change that alters the design, or that a user can see (the language,
an option, an output, the editor, a message), updates the documentation in
the same pull request.** A pull request that changes behaviour and leaves the
documents describing the old behaviour is not finished.

Where each thing is documented:

| change | update |
|---|---|
| the figure language (lexer, parser, printer) | `docs/tools/grammar.py`, then regenerate the EBNF block of `docs/LANGUAGE.md` (`--ebnf`) and the diagrams (`--svg docs/diagrams`); the prose and examples of `docs/LANGUAGE.md` |
| what the pictures show, or how they are drawn | `docs/NOTATION.md` (and `docs/MANUAL.md` for options); regenerate the pictures with `sh docs/tools/images.sh` (CI checks they are current) |
| a `framediag` option, an output file, a check | `docs/MANUAL.md` |
| the editor (`tools/framedit/`) | `docs/MANUAL.md`, section 4; the help texts in the page itself |
| a design decision, or a plan that changed | `docs/design/` (say what changed and when, rather than deleting the old reasoning) |
| anything a user would notice | `CHANGELOG.md`, in the section of the next version |
| a merged iteration (one or more pull requests released together) | raise `FregeDiagrams.version` (`FregeDiagrams/Version.lean`); head its `CHANGELOG.md` section with the version, the merge commit's short hash, its date and time (UTC) and the tag, if one is applied |

CI checks the mechanical part: the EBNF in `docs/LANGUAGE.md` must equal the
grammar, every example in it must parse, and the syntax diagrams and the
pictures in `docs/images/` must be regenerated. The rest is checked in review.

## Checks before a pull request

```bash
lake build
lake build FregeDiagrams.Test
lake exe framediag _build/check --check
python3 docs/tools/grammar.py --check docs/LANGUAGE.md
```

Default drawings of existing figures should stay byte-identical unless the
change is meant to alter them; say so in the pull request when it is.
