# NOTICE

Sagitta — The Computational Arrow of Time (Lean formalization).
Copyright 2026 Jose-de-Jesus Ulate-Cardenas. Licensed under the Apache License, Version 2.0.

This project contains code taken from **cslib-frontier** and **cslib** (both Apache-2.0),
copied without modification. See `VENDORED.md` for the exact repositories, commits and files,
`vendor/LICENSE-cslib-frontier`, `vendor/LICENSE-cslib` and `vendor/NOTICE-cslib-frontier`.

The file `Sagitta/Arrow/TM/Ising.lean` uses the encodings, verifiers and the `NP`-completeness of
MAX-CUT of cslib-frontier; the reduction from MAX-CUT to the Ising ground state follows
F. Barahona (1982).

It depends on **Mathlib** (Apache-2.0), https://github.com/leanprover-community/mathlib4, at
revision `bbff2954fe5ee3b7a4b33cc26ef873a1c3277d91`, fetched as a package (not vendored).

No code from formal-conjectures is included.

Parts of the code and documentation were written with AI assistance (Claude, by Anthropic); see
`README.md`.
