/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV/V — Finite packing LP over an ordered field: certificate contract.

Primal:  max Σ_i g i · x i   s.t. x ≥ 0,  Σ_i A i e · x i ≤ 1  (e : E)
Dual:    min Σ_e y e         s.t. y ≥ 0,  g i ≤ Σ_e A i e · y e  (i : I)

  * `gap_identity`                   (C1)  dual − primal = Σ_e y_e(1 − load_e) + Σ_i x_i(Σ_e A y − g_i)
  * `weak_duality`                          primal ≤ dual (no sign condition on `A` needed)
  * `equal_value_of_complementarity`, `complementarity_of_equal_value`: equality ⇔ all slack
                                            products vanish — the checkable certificate contract
  * `discarded_value_le`             (C2)  V-CLEAN: objects touching a bad resource set `B`, each of
                                            gain ≤ M, carry primal value ≤ M·|B|

Ported from the returned sources `ComplementaryCertificate` / `RoundingCleanup` (L05, L10) onto a
self-contained model; the structures are the minimal fields those proofs use. Generic in any ordered
field `K` (instantiate with `ℚ` for exact certificates or `ℝ`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace FiniteLP.Rat

variable {I E : Type*} [Fintype I] [Fintype E]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A feasible primal (fractional packing) for the incidence matrix `A`. -/
structure PrimalFeasible (A : I → E → K) where
  weight : I → K
  weight_nonneg : ∀ i, 0 ≤ weight i
  capacity : ∀ e, ∑ i, A i e * weight i ≤ 1

/-- A feasible dual (fractional cover) for `A` and gains `g`. -/
structure DualFeasible (A : I → E → K) (g : I → K) where
  price : E → K
  price_nonneg : ∀ e, 0 ≤ price e
  demand : ∀ i, g i ≤ ∑ e, A i e * price e

variable {A : I → E → K} {g : I → K}

def primalValue (g : I → K) (p : PrimalFeasible A) : K := ∑ i, g i * p.weight i

def dualValue (d : DualFeasible A g) : K := ∑ e, d.price e

/-- **(C1) Gap identity.** -/
theorem gap_identity (p : PrimalFeasible A) (d : DualFeasible A g) :
    dualValue d - primalValue g p =
      (∑ e, d.price e * (1 - ∑ i, A i e * p.weight i)) +
      ∑ i, p.weight i * ((∑ e, A i e * d.price e) - g i) := by
  have hswap : (∑ e, d.price e * (∑ i, A i e * p.weight i)) =
      ∑ i, p.weight i * (∑ e, A i e * d.price e) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro e _
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, mul_one]
  rw [hswap]
  have hcomm : (∑ i, p.weight i * g i) = ∑ i, g i * p.weight i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm]
  unfold dualValue primalValue
  ring

theorem slack_cap_nonneg (p : PrimalFeasible A) (d : DualFeasible A g) (e : E) :
    0 ≤ d.price e * (1 - ∑ i, A i e * p.weight i) :=
  mul_nonneg (d.price_nonneg e) (sub_nonneg.mpr (p.capacity e))

theorem slack_dem_nonneg (p : PrimalFeasible A) (d : DualFeasible A g) (i : I) :
    0 ≤ p.weight i * ((∑ e, A i e * d.price e) - g i) :=
  mul_nonneg (p.weight_nonneg i) (sub_nonneg.mpr (d.demand i))

/-- **Weak duality.** -/
theorem weak_duality (p : PrimalFeasible A) (d : DualFeasible A g) :
    primalValue g p ≤ dualValue d := by
  have h := gap_identity p d
  have h1 := Finset.sum_nonneg (fun e (_ : e ∈ Finset.univ) => slack_cap_nonneg p d e)
  have h2 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => slack_dem_nonneg p d i)
  linarith

/-- Vanishing slacks certify equality of values. -/
theorem equal_value_of_complementarity (p : PrimalFeasible A) (d : DualFeasible A g)
    (hcap : ∀ e, d.price e * (1 - ∑ i, A i e * p.weight i) = 0)
    (hdem : ∀ i, p.weight i * ((∑ e, A i e * d.price e) - g i) = 0) :
    primalValue g p = dualValue d := by
  have h := gap_identity p d
  simp only [hcap, hdem, Finset.sum_const_zero, add_zero] at h
  linarith

/-- Equality of values forces every slack product to vanish. -/
theorem complementarity_of_equal_value (p : PrimalFeasible A) (d : DualFeasible A g)
    (heq : primalValue g p = dualValue d) :
    (∀ e, d.price e * (1 - ∑ i, A i e * p.weight i) = 0) ∧
    (∀ i, p.weight i * ((∑ e, A i e * d.price e) - g i) = 0) := by
  have h := gap_identity p d
  rw [heq, sub_self] at h
  have hcs := Finset.sum_nonneg (fun e (_ : e ∈ Finset.univ) => slack_cap_nonneg p d e)
  have hds := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => slack_dem_nonneg p d i)
  have hz1 : (∑ e, d.price e * (1 - ∑ i, A i e * p.weight i)) = 0 := by linarith
  have hz2 : (∑ i, p.weight i * ((∑ e, A i e * d.price e) - g i)) = 0 := by linarith
  constructor
  · intro e
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => slack_cap_nonneg p d e)).mp hz1 e
      (Finset.mem_univ e)
  · intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => slack_dem_nonneg p d i)).mp hz2 i
      (Finset.mem_univ i)

/-- A primal/dual pair of equal value is optimal on both sides. -/
theorem optimal_of_equal (p : PrimalFeasible A) (d : DualFeasible A g)
    (heq : primalValue g p = dualValue d) :
    (∀ p' : PrimalFeasible A, primalValue g p' ≤ primalValue g p) ∧
    (∀ d' : DualFeasible A g, dualValue d ≤ dualValue d') := by
  constructor
  · intro p'; rw [heq]; exact weak_duality p' d
  · intro d'; rw [← heq]; exact weak_duality p d'

/-- **(C2) V-CLEAN.** Discarding the objects `D` that each touch the bad resource set `B` (total
incidence ≥ 1 on `B`) and each carry gain ≤ `M` loses primal value at most `M·|B|`. Coverage is
literal fractional load, not an injection. -/
theorem discarded_value_le (p : PrimalFeasible A) (D : Finset I) (B : Finset E) (M : K)
    (hA : ∀ i e, 0 ≤ A i e) (hM : 0 ≤ M)
    (hg : ∀ i ∈ D, g i ≤ M)
    (hcover : ∀ i ∈ D, 1 ≤ ∑ e ∈ B, A i e) :
    (∑ i ∈ D, g i * p.weight i) ≤ M * (B.card : K) := by
  classical
  have hload : ∀ e, (∑ i ∈ D, A i e * p.weight i) ≤ 1 := by
    intro e
    apply le_trans _ (p.capacity e)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
      (fun i _ _ => mul_nonneg (hA i e) (p.weight_nonneg i))
  have hswap : (∑ i ∈ D, (∑ e ∈ B, A i e) * p.weight i) =
      ∑ e ∈ B, ∑ i ∈ D, A i e * p.weight i := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  calc
    (∑ i ∈ D, g i * p.weight i) ≤ ∑ i ∈ D, M * p.weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hg i hi) (p.weight_nonneg i)
    _ = M * ∑ i ∈ D, p.weight i := by rw [Finset.mul_sum]
    _ ≤ M * ∑ i ∈ D, (∑ e ∈ B, A i e) * p.weight i := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Finset.sum_le_sum
      intro i hi
      simpa using mul_le_mul_of_nonneg_right (hcover i hi) (p.weight_nonneg i)
    _ = M * ∑ e ∈ B, ∑ i ∈ D, A i e * p.weight i := by rw [hswap]
    _ ≤ M * ∑ e ∈ B, (1 : K) := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact Finset.sum_le_sum (fun e _ => hload e)
    _ = M * (B.card : K) := by simp

end FiniteLP.Rat
