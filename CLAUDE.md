# Rules for Claude sessions in this repository

* **Documentation moves with the code** (CONTRIBUTING.md): any change to the
  design or to anything a user can see updates the documents in the same
  pull request. Check the table in CONTRIBUTING.md before opening a PR.
* The grammar has one source, `docs/tools/grammar.py`; regenerate the EBNF
  block of `docs/LANGUAGE.md` and `docs/diagrams/` from it, never edit them
  by hand.
* Changes reach `main` only by pull request; Matthew merges.
* Commits use the GitHub no-reply address configured in this clone; never
  put a personal email address in the repository.
* Plain technical English; state what is tested and what is proved
  separately (the round trip is tested, not proved).
