/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Strong duality for the finite rational packing LP (wave 2c, item "Farkas + strong duality").

PROVENANCE. Port of the returned handoff source `Erdos81/FiniteLPDuality.lean` (L24 of `CATALOGO_Y_ESTADO.md`,
delivery `ERDOS81_ENTREGA_LEAN_NUEVO_IV_Y_V_20260912`) onto Paper V's `FiniteLP` structures
(`ErdosPaperI/RationalLP.lean`, generic ordered field, here instantiated at `ℚ`): `PrimalFeasible`, `DualFeasible`,
`primalValue`, `dualValue`, `weak_duality` have the same fields/statements, so the proof is unchanged up to the
namespace. Input: `FiniteLP.Rat.farkas` (Fourier–Motzkin). Entire argument finite, rational, analysis-free.

  `exists_equal_primal_dual` : nonnegative incidence, every item uses some resource with coefficient ≥ 1
                               ⟹ a feasible packing and a feasible cover of EQUAL value exist (both optimal by
                               `weak_duality`; equality ⇔ complementary slackness by `RationalLP.lean`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import ErdosPaperI.RationalLP
public import ErdosPaperI.RationalFarkas

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

open scoped BigOperators

namespace FiniteLP.Rat

universe u v

variable {Item : Type u} {Resource : Type v}

/-- Variables of the combined primal/dual system: a primal weight per item and
a dual price per resource. -/
abbrev DualityVar (Item : Type u) (Resource : Type v) := Item ⊕ Resource

/-- Constraints of the combined primal/dual system: primal nonnegativity,
capacity, dual nonnegativity, demand, and the reversed duality inequality. -/
abbrev DualityCons (Item : Type u) (Resource : Type v) :=
  Item ⊕ Resource ⊕ Resource ⊕ Item ⊕ PUnit.{max u v + 1}

/-- The coefficient matrix of the combined primal/dual system. -/
def dualityMatrix [DecidableEq Item] [DecidableEq Resource]
    (incidence : Item → Resource → ℚ) (gain : Item → ℚ) :
    DualityCons Item Resource → DualityVar Item Resource → ℚ :=
  Sum.elim
    (fun i0 => Sum.elim (fun i => if i0 = i then (-1 : ℚ) else 0) (fun _ => 0))
    (Sum.elim
      (fun e0 => Sum.elim (fun i => incidence i e0) (fun _ => 0))
      (Sum.elim
        (fun e0 => Sum.elim (fun _ => 0) (fun e => if e0 = e then (-1 : ℚ) else 0))
        (Sum.elim
          (fun i0 => Sum.elim (fun _ => 0) (fun e => -incidence i0 e))
          (fun _ => Sum.elim (fun i => -gain i) (fun _ => 1)))))

/-- The right-hand side of the combined primal/dual system. -/
def dualityRhs (gain : Item → ℚ) : DualityCons Item Resource → ℚ :=
  Sum.elim (fun _ => 0)
    (Sum.elim (fun _ => 1)
      (Sum.elim (fun _ => 0)
        (Sum.elim (fun i0 => -gain i0) (fun _ => 0))))

section Duality

variable [Fintype Item] [Fintype Resource] [DecidableEq Item] [DecidableEq Resource]

/-- **Strong duality for the finite rational packing LP.**  If the incidence
matrix is nonnegative and every item uses some resource with coefficient at
least `1`, then a feasible packing and a feasible cover of equal value exist.
In particular both are optimal, by `FiniteLP.weak_duality`. -/
theorem exists_equal_primal_dual
    (incidence : Item → Resource → ℚ) (gain : Item → ℚ)
    (hnonneg : ∀ i e, 0 ≤ incidence i e)
    (hcover : ∀ i, ∃ e, 1 ≤ incidence i e) :
    ∃ p : PrimalFeasible incidence, ∃ d : DualFeasible incidence gain,
      primalValue gain p = dualValue d := by
  classical
  rcases FiniteLP.Rat.farkas (dualityMatrix incidence gain) (dualityRhs gain)
    with ⟨x, hx⟩ | ⟨y, hy⟩
  · -- a solution of the combined system gives the two witnesses
    have hsplit : ∀ j : DualityCons Item Resource,
        (∑ i, dualityMatrix incidence gain j (Sum.inl i) * x (Sum.inl i))
          + (∑ e, dualityMatrix incidence gain j (Sum.inr e) * x (Sum.inr e))
          ≤ dualityRhs gain j := by
      intro j
      have h := hx j
      rwa [Fintype.sum_sum_type] at h
    have hw0 : ∀ i, 0 ≤ x (Sum.inl i) := by
      intro i
      have h := hsplit (Sum.inl i)
      simp only [dualityMatrix, dualityRhs, Sum.elim_inl, Sum.elim_inr, ite_mul,
        neg_mul, one_mul, zero_mul, Finset.sum_const_zero, add_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      linarith
    have hcap : ∀ e, ∑ i, incidence i e * x (Sum.inl i) ≤ 1 := by
      intro e
      have h := hsplit (Sum.inr (Sum.inl e))
      simp only [dualityMatrix, dualityRhs, Sum.elim_inl, Sum.elim_inr, zero_mul,
        Finset.sum_const_zero, add_zero] at h
      exact h
    have hr0 : ∀ e, 0 ≤ x (Sum.inr e) := by
      intro e
      have h := hsplit (Sum.inr (Sum.inr (Sum.inl e)))
      simp only [dualityMatrix, dualityRhs, Sum.elim_inl, Sum.elim_inr, ite_mul,
        neg_mul, one_mul, zero_mul, Finset.sum_const_zero, zero_add,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      linarith
    have hdem : ∀ i, gain i ≤ ∑ e, incidence i e * x (Sum.inr e) := by
      intro i
      have h := hsplit (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp only [dualityMatrix, dualityRhs, Sum.elim_inl, Sum.elim_inr, zero_mul,
        neg_mul, Finset.sum_const_zero, zero_add, Finset.sum_neg_distrib] at h
      linarith
    have hgap : ∑ e, x (Sum.inr e) ≤ ∑ i, gain i * x (Sum.inl i) := by
      have h := hsplit (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
      simp only [dualityMatrix, dualityRhs, Sum.elim_inl, Sum.elim_inr, neg_mul,
        one_mul, Finset.sum_neg_distrib] at h
      linarith
    refine ⟨⟨fun i => x (Sum.inl i), hw0, hcap⟩, ⟨fun e => x (Sum.inr e), hr0, hdem⟩, ?_⟩
    have hle := weak_duality (⟨fun i => x (Sum.inl i), hw0, hcap⟩ : PrimalFeasible incidence)
      (⟨fun e => x (Sum.inr e), hr0, hdem⟩ : DualFeasible incidence gain)
    have hge : dualValue (⟨fun e => x (Sum.inr e), hr0, hdem⟩ : DualFeasible incidence gain)
        ≤ primalValue gain (⟨fun i => x (Sum.inl i), hw0, hcap⟩ : PrimalFeasible incidence) := by
      simpa [primalValue, dualValue] using hgap
    linarith
  · -- a Farkas certificate is impossible
    exfalso
    obtain ⟨hy0, hyk, hyb⟩ := hy
    have hsplitc : ∀ f : DualityCons Item Resource → ℚ,
        ∑ j, y j * f j
          = ((∑ i, y (Sum.inl i) * f (Sum.inl i))
            + ((∑ e, y (Sum.inr (Sum.inl e)) * f (Sum.inr (Sum.inl e)))
              + ((∑ e, y (Sum.inr (Sum.inr (Sum.inl e))) * f (Sum.inr (Sum.inr (Sum.inl e))))
                + ((∑ i, y (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
                      * f (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
                  + y (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
                      * f (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))))) := by
      intro f
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
        Fintype.sum_sum_type]
      simp
    set u : Item → ℚ := fun i => y (Sum.inl i) with hu
    set v : Resource → ℚ := fun e => y (Sum.inr (Sum.inl e)) with hv
    set s : Resource → ℚ := fun e => y (Sum.inr (Sum.inr (Sum.inl e))) with hs
    set t : Item → ℚ := fun i => y (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) with ht
    set lam : ℚ :=
      y (Sum.inr (Sum.inr (Sum.inr (Sum.inr (PUnit.unit : PUnit.{max u v + 1}))))) with hlam
    have hxi : ∀ i : Item, -u i + (∑ e, v e * incidence i e) - lam * gain i = 0 := by
      intro i
      have h := hyk (Sum.inl i)
      rw [hsplitc] at h
      simp only [dualityMatrix, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_neg, mul_one,
        mul_zero, Finset.sum_const_zero, zero_add, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h
      linarith
    have hye : ∀ e : Resource, -s e - (∑ i, t i * incidence i e) + lam = 0 := by
      intro e
      have h := hyk (Sum.inr e)
      rw [hsplitc] at h
      simp only [dualityMatrix, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_neg, mul_one,
        mul_zero, Finset.sum_const_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Finset.sum_neg_distrib] at h
      linarith
    have hrhs : (∑ e, v e) - (∑ i, t i * gain i) < 0 := by
      rw [hsplitc] at hyb
      simp only [dualityRhs, Sum.elim_inl, Sum.elim_inr, mul_zero, mul_one, mul_neg,
        Finset.sum_const_zero, add_zero, zero_add, Finset.sum_neg_distrib] at hyb
      linarith
    have hu0 : ∀ i, 0 ≤ u i := fun i => hy0 _
    have hv0 : ∀ e, 0 ≤ v e := fun e => hy0 _
    have hs0 : ∀ e, 0 ≤ s e := fun e => hy0 _
    have ht0 : ∀ i, 0 ≤ t i := fun i => hy0 _
    have hlam0 : 0 ≤ lam := hy0 _
    rcases lt_or_eq_of_le hlam0 with hlpos | hl0
    · -- positive multiplier: rescale into feasible primal and dual points
      have hcapP : ∀ e, ∑ i, incidence i e * (t i / lam) ≤ 1 := by
        intro e
        have h := hye e
        have hsum : ∑ i, incidence i e * (t i / lam)
            = (∑ i, t i * incidence i e) / lam := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hsum, div_le_one hlpos]
        have := hs0 e
        linarith
      have hdemD : ∀ i, gain i ≤ ∑ e, incidence i e * (v e / lam) := by
        intro i
        have h := hxi i
        have hsum : ∑ e, incidence i e * (v e / lam)
            = (∑ e, v e * incidence i e) / lam := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun e _ => by ring
        rw [hsum, le_div_iff₀ hlpos]
        have := hu0 i
        linarith
      have hweak := weak_duality
        (⟨fun i => t i / lam, fun i => div_nonneg (ht0 i) hlam0, hcapP⟩ :
          PrimalFeasible incidence)
        (⟨fun e => v e / lam, fun e => div_nonneg (hv0 e) hlam0, hdemD⟩ :
          DualFeasible incidence gain)
      simp only [primalValue, dualValue] at hweak
      have h1 : ∑ i, gain i * (t i / lam) = (∑ i, gain i * t i) / lam := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h2 : ∑ e, v e / lam = (∑ e, v e) / lam := (Finset.sum_div _ _ _).symm
      rw [h1, h2, div_le_div_iff₀ hlpos hlpos] at hweak
      have hgt : ∑ i, gain i * t i ≤ ∑ e, v e :=
        le_of_mul_le_mul_right hweak hlpos
      have hcomm : ∑ i, t i * gain i = ∑ i, gain i * t i :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hcomm] at hrhs
      linarith
    · -- zero multiplier: the item/resource condition kills the `t` part
      have hlz : lam = 0 := hl0.symm
      have htzero : ∀ i, t i = 0 := by
        intro i
        obtain ⟨e, he⟩ := hcover i
        have h := hye e
        rw [hlz] at h
        have hsum : ∑ i', t i' * incidence i' e = 0 := by
          have hse := hs0 e
          have hnn : 0 ≤ ∑ i', t i' * incidence i' e :=
            Finset.sum_nonneg fun i' _ => mul_nonneg (ht0 i') (hnonneg i' e)
          linarith
        have hall : ∀ i' ∈ (Finset.univ : Finset Item), 0 ≤ t i' * incidence i' e :=
          fun i' _ => mul_nonneg (ht0 i') (hnonneg i' e)
        have hterm : t i * incidence i e = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hall).mp hsum i (Finset.mem_univ i)
        have hpos : 0 < incidence i e := lt_of_lt_of_le zero_lt_one he
        rcases mul_eq_zero.mp hterm with h1 | h1
        · exact h1
        · exact absurd h1 (ne_of_gt hpos)
      have hsum0 : ∑ i, t i * gain i = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [htzero i, zero_mul]
      have hvnn : 0 ≤ ∑ e, v e := Finset.sum_nonneg fun e _ => hv0 e
      rw [hsum0] at hrhs
      linarith

end Duality

end FiniteLP.Rat
