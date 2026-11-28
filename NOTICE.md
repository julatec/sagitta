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

The map (`Sagitta/Map`) contains code adapted from **formal-conjectures** (Apache-2.0),
https://github.com/google-deepmind/formal-conjectures, commit
`2207c54d0dbe960de591d280f997b195bf3f6e28`, Copyright 2025-2026 The Formal Conjectures Authors
(`vendor/LICENSE-formal-conjectures`; the project has no NOTICE file at that commit):

* `Sagitta/Map/Codificacion.lean`, adapted from
  `FormalConjecturesForMathlib/Computability/BitstringEncoding.lean`;
* the definitions of `P`, `NP` and `coNP` in `Sagitta/Map/Clases.lean`, adapted from
  `FormalConjecturesForMathlib/Computability/Complexity.lean` and
  `FormalConjectures/Millennium/PvsNP.lean`.

These two files are **modified**, and each one says so in its header: identifiers in Spanish, no
module system, only the encoding instances that are used, a bit string is encoded as itself, and
open statements are propositions (`def … : Prop`) instead of theorems with `sorry`. No other file
of the map contains third-party code; the sources that the comments cite are cited, not copied.

Parts of the code and documentation were written with AI assistance (Claude, by Anthropic); see
`README.md`.
