/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Paper I — Affine profile reduction for fractional triangle packings in split graphs

J. P. Traverso Gianini, *Affine Profile Reduction for Fractional Triangle Packings in Split
Graphs* (Paper I of the Erdős #81 series, preprint v1.4). For a split graph `G` on `n` vertices,
with clique `Fin p`, independent vertices `ι` and neighbourhoods `N v ⊆ Fin p`, the deficit
`Φ(G) = |E(G)| − 2 ν₃*(G)`, where `ν₃*` is the fractional triangle packing number, satisfies

* `paperI_main_sharp`: `Φ(G) ≤ n²/6 + n/2` (the finite consequence stated in the paper);
* `paperI_main`: `Φ(G) ≤ n²/6 + n` (the bound of the first edition);
* `split_main`: the sharp bound restated for every finite `SimpleGraph` that is split
  (`IsSplit`, as in the registered entry `jtraverso/chordal-split-threshold-graphs`), with `ν₃*`
  defined through fractional triangle packings as in `jtraverso/asymptotic-triangle-packing`.

The definitions below are copied verbatim from the paper's Lean freeze (`lean_v1.2_freeze`) and
are part of the audited statements; the Mathlib definitions used are reproduced in
`MATHLIB_DEFINITIONS.md`.
-/

@[expose] public section

namespace ErdosPaperI
open scoped BigOperators
open Classical Finset

/-- A finite split graph: clique `Fin p`, independent index `ι`, neighborhoods `N v ⊆ Fin p`. -/
structure Split where
  p : ℕ
  ι : Type
  fι : Fintype ι
  N : ι → Finset (Fin p)

attribute [instance] Split.fι

namespace Split
variable (G : Split)

/-- Vertex count: p clique vertices + |ι| independent vertices. -/
def n : ℕ := G.p + Fintype.card G.ι

/-- |E(G)| = C(p,2) + Σ_v |N v|  (paper (2.1)). -/
def edgeCount : ℕ := Nat.choose G.p 2 + ∑ v : G.ι, (G.N v).card

/-- Edges of a split graph: clique edges `{i<j} ⊆ Fin p`, and cross edges `(v,x)` with `x ∈ N v`. -/
abbrev Edge (G : Split) : Type :=
  {e : Fin G.p × Fin G.p // e.1 < e.2} ⊕ {e : G.ι × Fin G.p // e.2 ∈ G.N e.1}

/-- Triangles of a split graph: clique triples `{i<j<k}`, and mixed triangles `{v,x,y}`
    with `x<y` both neighbors of the independent vertex `v`. -/
abbrev Triangle (G : Split) : Type :=
  {t : Fin G.p × Fin G.p × Fin G.p // t.1 < t.2.1 ∧ t.2.1 < t.2.2} ⊕
  {t : G.ι × Fin G.p × Fin G.p // t.2.1 < t.2.2 ∧ t.2.1 ∈ G.N t.1 ∧ t.2.2 ∈ G.N t.1}

/-- Edge–triangle incidence. -/
def edgeMem : Edge G → Triangle G → Prop
  | Sum.inl ⟨(i, j), _⟩, Sum.inl ⟨(a, b, c), _⟩ =>
      (i = a ∧ j = b) ∨ (i = a ∧ j = c) ∨ (i = b ∧ j = c)
  | Sum.inl ⟨(i, j), _⟩, Sum.inr ⟨(_, x, y), _⟩ => i = x ∧ j = y
  | Sum.inr _,           Sum.inl _            => False
  | Sum.inr ⟨(v, x), _⟩, Sum.inr ⟨(w, y, z), _⟩ => v = w ∧ (x = y ∨ x = z)

/-- A feasible fractional triangle packing: nonnegative weights whose per-edge load is ≤ 1. -/
def FeasiblePacking (w : Triangle G → ℝ) : Prop :=
  (∀ T, 0 ≤ w T) ∧
    ∀ e : Edge G, ∑ T ∈ Finset.univ.filter (fun T => edgeMem G e T), w T ≤ 1

/-- The set of achievable packing values. -/
def packingValues : Set ℝ := {s | ∃ w, FeasiblePacking G w ∧ s = ∑ T, w T}

/-- ν₃*(G): the fractional triangle packing number, as a supremum of feasible packing values. -/
noncomputable def nu3star : ℝ := sSup (packingValues G)

/-- The deficit functional Φ = |E| − 2 ν₃*. -/
noncomputable def Phi : ℝ := (G.edgeCount : ℝ) - 2 * nu3star G

end Split

/-! ### Paper I on Mathlib's `SimpleGraph`

The definitions below are copied verbatim from the author's registered entries
`jtraverso/chordal-split-threshold-graphs` and `jtraverso/asymptotic-triangle-packing`. -/

/-- A partition of the vertices into a clique and an independent set. -/
structure SplitPartition {V : Type*} (G : SimpleGraph V) where
  clique : Set V
  independent : Set V
  isClique : G.IsClique clique
  isIndepSet : G.IsIndepSet independent
  disjoint : Disjoint clique independent
  cover : clique ∪ independent = Set.univ

/-- A graph is split if it admits a split partition. -/
def IsSplit {V : Type*} (G : SimpleGraph V) : Prop := Nonempty (SplitPartition G)

/-- The edges of `G` with both endpoints in the vertex set `t`. -/
def edgesIn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

def IsFracTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t ≤ 1

/-- The fractional triangle packing number `ν₃*(G)`. -/
noncomputable def fracPackingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  sSup {s | ∃ w, IsFracTrianglePacking G w ∧ s = ∑ t ∈ G.cliqueFinset 3, w t}

/-- **Paper I, Theorem 1.1 (sharp form).** For every split graph `G`,
`|E(G)| − 2 ν₃*(G) ≤ n²/6 + n/2`. -/
theorem paperI_main_sharp (G : Split) : G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 := by
  sorry

/-- **Paper I, Theorem 1.1 (first edition).** For every split graph `G`,
`|E(G)| − 2 ν₃*(G) ≤ n²/6 + n`. -/
theorem paperI_main (G : Split) : G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) := by
  sorry

/-- **Paper I, Theorem 1.1 (sharp form), on `SimpleGraph`.** For every split graph `G` on `n`
vertices, `|E(G)| − 2 ν₃*(G) ≤ n²/6 + n/2`. -/
theorem split_main {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsSplit G) :
    (G.edgeFinset.card : ℝ) - 2 * fracPackingNumber G ≤
      (Fintype.card V : ℝ) ^ 2 / 6 + (Fintype.card V : ℝ) / 2 := by
  sorry

end ErdosPaperI

/-! ## Finite linear programming duality

Over `ℝ`: Farkas' lemma in inequality form and covering/packing strong duality (used in the proof of
the main theorems). Over `ℚ`: Farkas' lemma (a rational system `M x ≤ b` has a rational solution or a
nonnegative rational certificate of infeasibility) and strong duality for the rational packing LP
(from the author's Erdős #81 Paper V formalization). -/

namespace FiniteLPDuality

/-- **Farkas' lemma over `ℝ`** (inequality form). If `x ≥ 0, N x ≥ c` has no solution, there is
`y ≥ 0` with `Nᵀ y ≤ 0` and `⟨c, y⟩ > 0`. -/
theorem farkas_real {ι κ : Type*} [Fintype ι] [Fintype κ] (N : ι → κ → ℝ) (c : ι → ℝ)
    (hinfeas : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, N i j * y i ≤ 0) ∧ 0 < ∑ i, c i * y i := by
  sorry

/-- **Covering/packing strong duality over `ℝ`.** For a nonnegative incidence matrix `A` with
nonnegative capacities `r`, in which every column has a positive entry, some packing attains the
covering optimum. -/
theorem covering_packing_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (r : ι → ℝ) (hA : ∀ e t, 0 ≤ A e t) (hr : ∀ e, 0 ≤ r e)
    (hcol : ∀ t, ∃ e, 0 < A e t) :
    ∃ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, (∑ t, A e t * w t) ≤ r e) ∧
      (∑ t, w t) = sInf {v : ℝ | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
        (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
  sorry

/-- **Farkas' lemma over `ℚ`.** A finite rational system `M x ≤ b` has a rational solution, or a
nonnegative rational certificate `y` with `yᵀ M = 0` and `⟨y, b⟩ < 0`. -/
theorem farkas_rat {J N : Type*} [Fintype J] [Fintype N] (M : J → N → ℚ) (b : J → ℚ) :
    (∃ x : N → ℚ, ∀ j, ∑ k, M j k * x k ≤ b j) ∨
      ∃ y : J → ℚ, (∀ j, 0 ≤ y j) ∧ (∀ k, ∑ j, y j * M j k = 0) ∧ ∑ j, y j * b j < 0 := by
  sorry

/-- **Strong duality for the rational packing LP.** If the incidence matrix is nonnegative and every
item uses some resource with coefficient at least `1`, a packing (`w ≥ 0`, `∑ᵢ A i e wᵢ ≤ 1`) and a
cover (`p ≥ 0`, `gᵢ ≤ ∑ₑ A i e pₑ`) of equal value exist; both are therefore optimal. -/
theorem packing_duality_rat {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (A : I → E → ℚ) (g : I → ℚ) (hA : ∀ i e, 0 ≤ A i e) (hcover : ∀ i, ∃ e, 1 ≤ A i e) :
    ∃ (w : I → ℚ) (p : E → ℚ), (∀ i, 0 ≤ w i) ∧ (∀ e, ∑ i, A i e * w i ≤ 1) ∧
      (∀ e, 0 ≤ p e) ∧ (∀ i, g i ≤ ∑ e, A i e * p e) ∧ ∑ i, g i * w i = ∑ e, p e := by
  sorry

end FiniteLPDuality
