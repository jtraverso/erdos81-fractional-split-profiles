/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import ErdosPaperI.SimpleGraphBridge

/-!
# Sanity checks for the `SimpleGraph` bridge

Three small split graphs, each with an explicit identification `Fin p ⊕ Fin m ≃ V`
(`finSumFinEquiv`: clique part first, independent part second):

* the triangle `K₃ = ⊤ : SimpleGraph (Fin 3)` (`p = 3`, `m = 0`): `|E| = 3`, `ν₃* = τ₃* = 1`;
* the star `K₁,₃` on `Fin 4` with centre `0` (`p = 1`, `m = 3`): `|E| = 3`, `ν₃* = τ₃* = 0`;
* the empty graph `⊥ : SimpleGraph (Fin 2)` (`p = 0`, `m = 2`): `|E| = 0`, `ν₃* = τ₃* = 0`.

For each we check that the graph is split, that the bridge hypotheses hold for the chosen
identification, that the split model has the expected `edgeCount` and `n` (computed directly
by `decide`, independently of the bridge), that the bridge identifies them with `|E(G)|` and
`|V|`, and that `nu3star` of the model equals the independently computed `ν₃*(G)`.
-/

@[expose] public section

namespace PaperI.Sanity
open Finset

/-- A graph without triangles has `ν₃* = 0`. -/
theorem fracPackingNumber_eq_zero_of_cliqueFinset_eq_empty {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.cliqueFinset 3 = ∅) :
    fracPackingNumber G = 0 := by
  apply le_antisymm
  · refine csSup_le ⟨0, fun _ => 0, isFracTrianglePacking_zero G, by simp⟩ ?_
    rintro _ ⟨w, -, rfl⟩
    simp [h]
  · simpa [h] using le_fracPackingNumber G (isFracTrianglePacking_zero G)

/-! ### The triangle `K₃` -/

/-- `K₃` with clique part `Fin 3` and empty independent part. -/
def eK3 : Fin 3 ⊕ Fin 0 ≃ Fin 3 := finSumFinEquiv

theorem K3_isSplit : IsSplit (⊤ : SimpleGraph (Fin 3)) :=
  ⟨{ clique := Set.univ, independent := ∅,
     isClique := fun _ _ _ _ h => (SimpleGraph.top_adj _ _).mpr h,
     isIndepSet := Set.pairwise_empty _,
     disjoint := Set.disjoint_empty _,
     cover := Set.union_empty _ }⟩

theorem K3_hcl : ∀ i j : Fin 3, i ≠ j →
    (⊤ : SimpleGraph (Fin 3)).Adj (eK3 (Sum.inl i)) (eK3 (Sum.inl j)) := by decide

theorem K3_hind : ∀ a b : Fin 0,
    ¬ (⊤ : SimpleGraph (Fin 3)).Adj (eK3 (Sum.inr a)) (eK3 (Sum.inr b)) := by decide

theorem K3_card_edgeFinset : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide

theorem K3_cliqueFinset : (⊤ : SimpleGraph (Fin 3)).cliqueFinset 3 = {univ} := by decide

theorem K3_model_edgeCount : (Split.ofEquiv (⊤ : SimpleGraph (Fin 3)) eK3).edgeCount = 3 := by
  decide

theorem K3_model_n : (Split.ofEquiv (⊤ : SimpleGraph (Fin 3)) eK3).n = 3 := by decide

theorem K3_bridge_edgeCount :
    (Split.ofEquiv (⊤ : SimpleGraph (Fin 3)) eK3).edgeCount =
      (⊤ : SimpleGraph (Fin 3)).edgeFinset.card :=
  Split.ofEquiv.edgeCount_eq K3_hcl K3_hind

theorem K3_bridge_n : (Split.ofEquiv (⊤ : SimpleGraph (Fin 3)) eK3).n = Fintype.card (Fin 3) :=
  Split.ofEquiv.n_eq

/-- `ν₃*(K₃) = 1`: the triangle with weight `1` is a packing, and one edge with weight `1` is a
cover. -/
theorem K3_fracPackingNumber : fracPackingNumber (⊤ : SimpleGraph (Fin 3)) = 1 := by
  apply le_antisymm
  · refine csSup_le ⟨0, fun _ => 0, isFracTrianglePacking_zero _, by simp⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    have hy : IsFracTriangleCover (⊤ : SimpleGraph (Fin 3))
        (fun e => if e = s(0, 1) then 1 else 0) := by
      refine ⟨fun e => by dsimp only; split_ifs <;> norm_num, fun t ht => ?_⟩
      rw [K3_cliqueFinset, mem_singleton] at ht
      subst ht
      have hmem : s(0, 1) ∈ edgesIn (⊤ : SimpleGraph (Fin 3)) univ := by decide
      exact le_trans (by simp) (single_le_sum (fun e _ => by split_ifs <;> norm_num) hmem)
    refine le_trans (packing_le_cover _ hw hy) (le_of_eq ?_)
    simp
  · have hw : IsFracTrianglePacking (⊤ : SimpleGraph (Fin 3)) (fun _ => 1) := by
      refine ⟨fun _ => zero_le_one, fun e _ => ?_⟩
      rw [K3_cliqueFinset]
      exact le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun _ _ _ => zero_le_one) (by simp)
    simpa [K3_cliqueFinset] using le_fracPackingNumber _ hw

theorem K3_fracCoverNumber : fracCoverNumber (⊤ : SimpleGraph (Fin 3)) = 1 := by
  rw [fracCoverNumber_eq_fracPackingNumber, K3_fracPackingNumber]

theorem K3_model_nu3star : (Split.ofEquiv (⊤ : SimpleGraph (Fin 3)) eK3).nu3star = 1 := by
  rw [Split.ofEquiv.nu3star_eq K3_hcl K3_hind, K3_fracPackingNumber]

/-- The main bound for `K₃`: `3 − 2·1 ≤ 3²/6 + 3/2`. -/
example : ((⊤ : SimpleGraph (Fin 3)).edgeFinset.card : ℝ) -
    2 * fracPackingNumber (⊤ : SimpleGraph (Fin 3)) ≤
      (Fintype.card (Fin 3) : ℝ) ^ 2 / 6 + (Fintype.card (Fin 3) : ℝ) / 2 :=
  split_main _ K3_isSplit

/-! ### The star `K₁,₃` -/

/-- The star on `Fin 4` with centre `0`. -/
def star : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun a _ => a = 0

instance : DecidableRel star.Adj := fun a b =>
  decidable_of_iff (a ≠ b ∧ (a = 0 ∨ b = 0)) (by rw [star, SimpleGraph.fromRel_adj])

/-- The star with clique part `{0}` and independent part `{1, 2, 3}`. -/
def eStar : Fin 1 ⊕ Fin 3 ≃ Fin 4 := finSumFinEquiv

theorem star_isSplit : IsSplit star :=
  ⟨{ clique := {0}, independent := {x | x ≠ 0},
     isClique := Set.pairwise_singleton _ _,
     isIndepSet := by
       intro a ha b hb _ h
       rw [star, SimpleGraph.fromRel_adj] at h
       rcases h.2 with h | h
       · exact ha h
       · exact hb h,
     disjoint := Set.disjoint_left.mpr fun a ha hb => hb ha,
     cover := by ext x; by_cases hx : x = 0 <;> simp [hx] }⟩

theorem star_hcl : ∀ i j : Fin 1, i ≠ j → star.Adj (eStar (Sum.inl i)) (eStar (Sum.inl j)) := by
  decide

theorem star_hind : ∀ a b : Fin 3, ¬ star.Adj (eStar (Sum.inr a)) (eStar (Sum.inr b)) := by
  decide

theorem star_card_edgeFinset : star.edgeFinset.card = 3 := by decide

theorem star_cliqueFinset : star.cliqueFinset 3 = ∅ := by decide

theorem star_model_edgeCount : (Split.ofEquiv star eStar).edgeCount = 3 := by decide

theorem star_model_n : (Split.ofEquiv star eStar).n = 4 := by decide

theorem star_bridge_edgeCount :
    (Split.ofEquiv star eStar).edgeCount = star.edgeFinset.card :=
  Split.ofEquiv.edgeCount_eq star_hcl star_hind

theorem star_fracPackingNumber : fracPackingNumber star = 0 :=
  fracPackingNumber_eq_zero_of_cliqueFinset_eq_empty _ star_cliqueFinset

theorem star_fracCoverNumber : fracCoverNumber star = 0 := by
  rw [fracCoverNumber_eq_fracPackingNumber, star_fracPackingNumber]

theorem star_model_nu3star : (Split.ofEquiv star eStar).nu3star = 0 := by
  rw [Split.ofEquiv.nu3star_eq star_hcl star_hind, star_fracPackingNumber]

/-! ### The empty graph on two vertices -/

/-- The empty graph with empty clique part and independent part `Fin 2`. -/
def eEmpty : Fin 0 ⊕ Fin 2 ≃ Fin 2 := finSumFinEquiv

theorem empty_isSplit : IsSplit (⊥ : SimpleGraph (Fin 2)) :=
  ⟨{ clique := ∅, independent := Set.univ,
     isClique := Set.pairwise_empty _,
     isIndepSet := fun _ _ _ _ _ h => h,
     disjoint := Set.empty_disjoint _,
     cover := Set.empty_union _ }⟩

theorem empty_hcl : ∀ i j : Fin 0, i ≠ j →
    (⊥ : SimpleGraph (Fin 2)).Adj (eEmpty (Sum.inl i)) (eEmpty (Sum.inl j)) := by decide

theorem empty_hind : ∀ a b : Fin 2,
    ¬ (⊥ : SimpleGraph (Fin 2)).Adj (eEmpty (Sum.inr a)) (eEmpty (Sum.inr b)) := by decide

theorem empty_card_edgeFinset : (⊥ : SimpleGraph (Fin 2)).edgeFinset.card = 0 := by simp

theorem empty_model_edgeCount : (Split.ofEquiv (⊥ : SimpleGraph (Fin 2)) eEmpty).edgeCount = 0 := by
  decide

theorem empty_model_n : (Split.ofEquiv (⊥ : SimpleGraph (Fin 2)) eEmpty).n = 2 := by decide

theorem empty_bridge_edgeCount :
    (Split.ofEquiv (⊥ : SimpleGraph (Fin 2)) eEmpty).edgeCount =
      (⊥ : SimpleGraph (Fin 2)).edgeFinset.card := by
  convert Split.ofEquiv.edgeCount_eq empty_hcl empty_hind

theorem empty_fracPackingNumber : fracPackingNumber (⊥ : SimpleGraph (Fin 2)) = 0 :=
  fracPackingNumber_eq_zero_of_cliqueFinset_eq_empty _ (by decide)

theorem empty_fracCoverNumber : fracCoverNumber (⊥ : SimpleGraph (Fin 2)) = 0 := by
  rw [fracCoverNumber_eq_fracPackingNumber, empty_fracPackingNumber]

theorem empty_model_nu3star : (Split.ofEquiv (⊥ : SimpleGraph (Fin 2)) eEmpty).nu3star = 0 := by
  rw [Split.ofEquiv.nu3star_eq empty_hcl empty_hind, empty_fracPackingNumber]

end PaperI.Sanity
