/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import ErdosPaperI.Sharp
public import ErdosPaperI.SimpleGraphBridge

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `Challenge.lean`. A split graph of the Challenge is
transported to the library's `PaperI.Split` (same fields); the library's definitions of `n` and
`Φ` are literally the same, so the main theorems transfer.

The `SimpleGraph` statement `split_main` is transported to the library copies of the same
definitions in `ErdosPaperI/SimpleGraphBridge.lean` (namespace `PaperI`), where it is proved.
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

/-! ### Paper I on Mathlib's `SimpleGraph` (definitions copied verbatim from `Challenge.lean`) -/

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

/-- The same split graph, as a `PaperI.Split` of the library. -/
def Split.toLib (G : Split) : PaperI.Split := ⟨G.p, G.ι, G.fι, G.N⟩

/-- Transfer of the edge–triangle incidence along `Split.toLib`. -/
theorem Split.toLib_edgeMem (G : Split) (e : G.Edge) (T : G.Triangle) :
    G.toLib.edgeMem e T ↔ G.edgeMem e T := by
  rcases e with ⟨⟨i, j⟩, h⟩ | ⟨⟨v, x⟩, h⟩ <;> rcases T with ⟨⟨a, b, c⟩, h'⟩ | ⟨⟨w, y, z⟩, h'⟩ <;>
    exact Iff.rfl

/-- Transfer of feasibility of a packing along `Split.toLib`. -/
theorem Split.toLib_feasiblePacking (G : Split) (w : G.Triangle → ℝ) :
    G.toLib.FeasiblePacking w ↔ G.FeasiblePacking w := by
  have hfilter : ∀ e : G.Edge, (Finset.univ.filter (fun T => G.toLib.edgeMem e T)) =
      Finset.univ.filter (fun T => G.edgeMem e T) := by
    intro e; ext T
    exact (Finset.mem_filter.trans (and_congr Iff.rfl (G.toLib_edgeMem e T))).trans
      (@Finset.mem_filter _ (fun T => G.edgeMem e T)
        (fun T => Classical.propDecidable _) _ _).symm
  unfold PaperI.Split.FeasiblePacking Split.FeasiblePacking
  exact and_congr Iff.rfl (forall_congr' fun e =>
    Iff.of_eq (congrArg (fun s => ∑ T ∈ s, w T ≤ 1) (hfilter e)))

/-- Transfer of the set of packing values along `Split.toLib`. -/
theorem Split.toLib_packingValues (G : Split) : G.toLib.packingValues = G.packingValues := by
  ext s
  unfold PaperI.Split.packingValues Split.packingValues
  simp only [Set.mem_ofPred_eq]
  exact exists_congr fun w => and_congr (G.toLib_feasiblePacking w) Iff.rfl

/-- Transfer of the vertex count along `Split.toLib`. -/
theorem Split.toLib_n (G : Split) : G.toLib.n = G.n := rfl

/-- Transfer of the deficit functional `Φ` along `Split.toLib`. -/
theorem Split.toLib_Phi (G : Split) : G.toLib.Phi = G.Phi := by
  have h1 : G.toLib.edgeCount = G.edgeCount := rfl
  unfold PaperI.Split.Phi Split.Phi PaperI.Split.nu3star Split.nu3star
  rw [h1, G.toLib_packingValues]

/-- **Paper I, Theorem 1.1 (sharp form).** For every split graph `G`,
`|E(G)| − 2 ν₃*(G) ≤ n²/6 + n/2`. -/
theorem paperI_main_sharp (G : Split) : G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 := by
  rw [← G.toLib_Phi, ← G.toLib_n]
  exact PaperI.Split.paperI_main_sharp G.toLib

/-- **Paper I, Theorem 1.1 (first edition).** For every split graph `G`,
`|E(G)| − 2 ν₃*(G) ≤ n²/6 + n`. -/
theorem paperI_main (G : Split) : G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) := by
  rw [← G.toLib_Phi, ← G.toLib_n]
  exact PaperI.paperI_main G.toLib

/-! ### Transfer of the `SimpleGraph` definitions to the library -/

/-- A split partition of `G` is a split partition in the sense of the library. -/
theorem IsSplit.toLib {V : Type*} {G : SimpleGraph V} (hG : IsSplit G) : PaperI.IsSplit G :=
  let ⟨P⟩ := hG
  ⟨⟨P.clique, P.independent, P.isClique, P.isIndepSet, P.disjoint, P.cover⟩⟩

/-- Transfer of `ν₃*` to the library. -/
theorem fracPackingNumber_eq_lib {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : fracPackingNumber G = PaperI.fracPackingNumber G := rfl

/-- **Paper I, Theorem 1.1 (sharp form), on `SimpleGraph`.** For every split graph `G` on `n`
vertices, `|E(G)| − 2 ν₃*(G) ≤ n²/6 + n/2`. -/
theorem split_main {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsSplit G) :
    (G.edgeFinset.card : ℝ) - 2 * fracPackingNumber G ≤
      (Fintype.card V : ℝ) ^ 2 / 6 + (Fintype.card V : ℝ) / 2 := by
  rw [fracPackingNumber_eq_lib]
  exact PaperI.split_main G hG.toLib

end ErdosPaperI
