# Erdős Problem 105, variant `n − 4`: `erdos_105.variants.sub_four`

A Lean 4 / Mathlib disproof of the statement `Erdos105.erdos_105.variants.sub_four` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/105.lean`, pinned to commit `e754a78c`, 2026-10-17):

> Let `A, B ⊂ ℝ²` be disjoint finite sets with `|A| = |B| + 4` and `A` not collinear.
> Is there a line through two points of `A` that contains no point of `B`?

The answer is **no**. The file proves the negation of the declaration's proposition, as the
repository's `question` convention asks for a negative answer.

Counterexample (Core_65536, [forum thread 105](https://www.erdosproblems.com/forum/thread/105),
24 July 2026): `A` = {(168,0), (280,560), (280,140), (420,630), (360,240), (504,672), (280,−280),
(420,0), (840,840), (0,−840)} (10 points) and `B` = {(0,420), (840,3360), (336,336), (280,0),
(420,315), (−840,−2520)} (6 points). The 45 pairs of points of `A` span 18 lines and each of them
contains a point of `B`; `A` is not collinear; `A ∩ B = ∅`. The incidences are checked by exact
integer arithmetic (`decide` on a determinant condition), and the determinant condition is
converted to membership in `line[ℝ, p, q]`.

## Build and check

```
lake exe cache get
lake build
lake env lean Erdos105SubFour.lean   # prints the axioms
```

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no
`native_decide`.

## Provenance / AI usage

The proof was produced by an automated prover (Claude Opus 5.5 run through Claude Code, 2026-10-18,
5 minutes wall-clock) given the counterexample as a hint, inside a harness that only allows edits
to the proof region and re-checks the result with an independent full compile. The statement was
not modified. A human read the statement against the problem page, re-checked the 45 incidences
numerically, and read the proof as mathematics before publication.
