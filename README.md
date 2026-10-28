# Fractional triangle packings in split graphs (Erdős #81, Paper I) in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the main result of the preprint *Affine Profile Reduction for
Fractional Triangle Packings in Split Graphs* (Erdős #81 series, Paper I, v1.4,
[doi:10.5281/zenodo.23478825](https://doi.org/10.5281/zenodo.23478825); series repository
[jtraverso/erdos-81-chordal-clique-partitions](https://github.com/jtraverso/erdos-81-chordal-clique-partitions)).

For a finite graph `G` let `ν₃*(G)` be the fractional triangle packing number: the largest total
weight of a nonnegative weighting of the triangles with load at most one on every edge.

| Lean (namespace `ErdosPaperI`) | Statement |
|---|---|
| `paperI_main_sharp` | For every split graph in the finite model of the paper, `|E| − 2ν₃* ≤ n²/6 + n/2`. |
| `paperI_main` | The bound `|E| − 2ν₃* ≤ n²/6 + n` of the first edition. |
| `split_main` | `|E(G)| − 2ν₃*(G) ≤ n²/6 + n/2` for every split `SimpleGraph` on a finite type. |

**Finite LP duality** (version 2), the linear-programming tool of the series:

| Lean (namespace `FiniteLPDuality`) | Statement |
|---|---|
| `farkas_real` | Farkas' lemma over `ℝ`: if `x ≥ 0, N x ≥ c` has no solution, some `y ≥ 0` has `Nᵀ y ≤ 0` and `⟨c, y⟩ > 0`. |
| `covering_packing_duality` | Covering/packing strong duality over `ℝ` (nonnegative incidences and capacities): some packing attains the covering optimum. |
| `farkas_rat` | Farkas' lemma over `ℚ`: `M x ≤ b` has a rational solution, or a certificate `y ≥ 0` with `yᵀ M = 0` and `⟨y, b⟩ < 0`. |
| `packing_duality_rat` | Strong duality for the rational packing LP: a packing and a cover of equal value exist. |

The real-valued results are the ones used in this paper; the rational ones (Fourier–Motzkin
elimination, no analysis) come from the author's Lean formalization of Paper V of the series.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the three statements; it imports only
  Mathlib. The finite split model (`Split`, its edges, triangles, feasible packings, `ν₃*`, `Φ`)
  is copied from the Lean freeze of the paper; `SplitPartition` and `IsSplit` are copied verbatim
  from [PALOMAR-2026-10-18-000006](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-18-000006&version=1)
  and `edgesIn`, `IsFracTrianglePacking` from
  [PALOMAR-2026-10-15-000011](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000011&version=1).
- [`Solution.lean`](Solution.lean) and [`ErdosPaperI/`](ErdosPaperI): the proofs.
  `Statement.lean` (finite model and the profile reduction), `Sharp.lean` (the sharp bound),
  `FiniteLPDuality.lean` (finite LP duality over `ℝ`), `RationalFarkas.lean`, `RationalLP.lean` and
  `StrongDuality.lean` (duality over `ℚ`), `SimpleGraphBridge.lean` (the `SimpleGraph`
  form) and `SimpleGraphBridgeSanity.lean` (checks on small graphs).
- [`comparator.json`](comparator.json), [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md),
  [`formalization.yaml`](formalization.yaml).

## How the proof goes

The fractional packing problem on a split graph reduces to the neighbourhood profiles of the
independent vertices and then to a three-variable linear program; finite LP duality certifies the
optimum. The resulting identity bounds `Φ = |E| − 2ν₃*` by `(p + q)²/6 + p/2 + b₁`, and the
quadratic slack in `b₁` pays for the linear term, giving `n²/6 + n/2`. The `SimpleGraph` form is
obtained through an explicit identification of a split partition with the finite model.

## Provenance and checks

The proofs come from the Lean freeze `lean_v1.2_freeze` of the author (Lean 4.28), produced with
Harmonic's Aristotle under the direction of the author, ported to Lean `v4.35.0-rc3` and the module
system with Aristotle and Claude (Claude Code). Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`: `lake build`; no `sorry`; `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound`; the elaborated statements and definitions of the
Challenge and the Solution are identical (`pp.all`). The rational duality modules come from the
author's Paper V formalization (series collection
[doi:10.5281/zenodo.23479507](https://doi.org/10.5281/zenodo.23479507)), with namespaces renamed.
