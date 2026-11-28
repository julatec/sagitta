# The blueprint: how it is written

The blueprint puts each definition and theorem of the Lean development in LaTeX next to its Lean
name. It is built with [leanblueprint](https://github.com/PatrickMassot/leanblueprint); the CI
builds it, checks every Lean name with `checkdecls`, and publishes it from `main`.

This file is for whoever writes or reviews a chapter.

## Structure

| Part | Chapters | Files |
|---|---|---|
| I. The arrow | the model, the laws, the localization, the decision hypothesis, Bennett, the consequences | `src/chapters/*.tex` |
| II. The map | how to read it, then one chapter per area (below) | `src/chapters/map/*.tex` |
| III. Hypotheses and fidelity | the named hypotheses of both parts; the table of comparisons with the sources | `src/chapters/hypotheses.tex`, `src/chapters/fidelity.tex` |

The chapters of the map, with the key of each one (the file is `src/chapters/map/KEY.tex`):

| Key | Chapter |
|---|---|
| `machines` | Machines and classes |
| `search` | Search and decision |
| `dynamics` | Dynamics and conservation |
| `information` | Information and Kolmogorov complexity |
| `arithmetic` | Bounded arithmetic and logic |
| `structure` | The structure of NP and dichotomies |
| `barriers` | Barriers and symmetries |
| `physics` | Physics: the Ising model |
| `infinite` | The infinite, the continuum and ordinals |
| `scales` | Scales, fractals and dimension |
| `arrow` | The arrow and the laws, seen from the map |

`src/content.tex` lists the chapters; `src/macros/common.tex` has the macros. A chapter is written
in its own file and in its file of references, `src/chapters/map/KEY-refs.tex`. Nothing else needs
to change to write a chapter, so two chapters can be written at the same time.

## An entry

One entry per central definition or theorem. Lemmas that only serve one proof do not get an entry.

```latex
\begin{theorem}[Midpoint search decides reachability, on a finite graph of configurations]
  \label{thm:machines-savitch}
  \lean{Sagitta.Map.Tiempo.savitch}
  \leanok
  \uses{def:machines-reach, def:machines-midpoint}
  % uses-lean: Sagitta.Map.Tiempo.cuasi
  Let $R$ be a step relation on a finite type $C$ of configurations, and $u, v \in C$. Then $v$ is
  reachable from $u$ in some number of steps if and only if the midpoint search of depth
  $\lceil \log_2 |C| \rceil$ accepts $(u, v)$.
  \source{\cite{Savitch70}.}
  \fidelity{Not checked against the printed source.}
  \leanfile{Sagitta/Map/Savitch.lean}
\end{theorem}

\begin{proof}
  \leanok
  The search of depth $i$ accepts exactly the pairs joined by at most $2^i$ steps, and a path
  between two of $|C|$ configurations can be taken without repetitions.
\end{proof}
```

The Lean statement is
`(∃ t, Alcanza R t u v) ↔ alc R (Nat.clog 2 (Fintype.card C)) u v = true`: about a relation on a
finite type, with no machine and no measure of space in it. So the title does not say "Savitch's
theorem", the statement has the finiteness of $C$ and the depth as Lean has them, and the fidelity
note stays as it is until someone compares the statement with the paper.

1. **The statement comes from the Lean statement**, not from memory and not from a textbook. Every
   hypothesis, quantifier and bound of the Lean signature is in the LaTeX. If Lean assumes a named
   hypothesis, the entry says "Assume …" and `\uses` the entry of that hypothesis.
2. **The model is part of the statement.** If the Lean result is about a graph of configurations,
   an abstract cost model or a circuit, the statement and the title say so. A statement about a
   relation on a finite type is a different claim from the theorem for machines that it comes from.
3. **`\lean{...}`** has the full names, exactly as in Lean, with every namespace
   (`Sagitta.Map.Tiempo.savitch`, not `savitch`). The identifiers of the map are in Spanish; they
   are not translated. Several names are separated by commas.
4. **`\leanok`** in the statement says that it is formalized; in the proof, that the proof is
   complete. The repository has no `sorry`, so every entry has both. An entry that is only a
   definition has no proof environment.
5. **Kind of entry**, one of:
   - a result of the literature: `\source{...}` with a `\cite`, and `\fidelity{...}`;
   - a definition or statement of this project: `\own{}`;
   - a tool for other entries: `\own{}` and `\infrastructure{}`;
   - the record of an attempt: `\own{}` and `\exploration{}`.
6. **`\fidelity{Not checked against the printed source.}`** is the note of an entry whose Lean
   statement has not been compared with the publication. It is replaced only by whoever has made
   the comparison, with what was found: the same statement, a weaker one, another model. When in
   doubt, the note stays.
7. **A named hypothesis** is a definition of type `Prop`. Its entry is a `definition` whose title
   begins with "Hypothesis:", and its `\leanok` says that the definition exists, never that the
   hypothesis holds.
8. **`\leanfile{...}`** gives the path of the Lean file from the root of the repository.

## Labels and dependencies

- Labels have the form `kind:KEY-slug`, with `kind` one of `chap`, `sec`, `def`, `thm`, `lem`,
  `prop`, `cor`, and `KEY` the key of the chapter: `def:machines-config-tree`. The key keeps the
  labels of two chapters apart.
- `\uses{...}` lists the labels of the entries that the statement or the proof needs: those of the
  same chapter and those of Part I.
- A dependency on an entry of another chapter of the map is written as a comment with the Lean
  name, `% uses-lean: Full.Lean.Name`, one or more names separated by commas. The labels of the
  other chapter may not exist yet; the comments are turned into `\uses` when the chapters are put
  together.

## References

- A chapter adds its references to `src/chapters/map/KEY-refs.tex`, as `\bibitem` entries in the
  style of `src/chapters/references.tex`. A key that is already in `references.tex` is used as it
  is, not defined again.
- A reference is written from the publication or from a bibliographic record, not from memory. An
  entry that has not been checked ends its first line with `% unverified`:
  `\bibitem{Savitch70} % unverified`.

## Style

English. Plain statements: no adjectives of praise, no comparisons with other work, no claims
about what a result means beyond what it states. Open problems are called open. A result in a
small model is not presented as the theorem for machines.

## Checking

```
blueprint/tools/check_names.sh --list blueprint/decl_names.txt
```

checks, without Lean and without plasTeX: that every name of every `\lean{...}` and of every
`% uses-lean:` comment is a declaration of the repository; that no label is defined twice, that
every label of `\uses` exists, and that the labels of a chapter of the map begin with its key; that
no reference is defined twice and that every `\cite` has one. It exits with an error when
something fails.

The list `blueprint/decl_names.txt` is made once, after `lake build`, with
`blueprint/tools/check_names.sh --make-list`. It has the declarations of this repository; a name of
Mathlib is checked only by the full check.

```
blueprint/tools/check_names.sh
```

is the full check: the same, with `lake exe checkdecls` instead of the list. It loads the compiled
project, which takes a few minutes, and it is what the CI runs.

The printed version is built with `latexmk -output-directory=../print print.tex` from
`blueprint/src` (XeLaTeX); an undefined reference there is an error of the chapter.
