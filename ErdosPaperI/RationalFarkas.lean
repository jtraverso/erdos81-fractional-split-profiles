/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Farkas' lemma over ℚ by Fourier–Motzkin elimination (wave 2c, item "Farkas + strong duality").

PROVENANCE. Verbatim port of the returned handoff source `Erdos81/RationalFarkas.lean` (L23 of
`CATALOGO_Y_ESTADO.md`, delivery `ERDOS81_ENTREGA_LEAN_NUEVO_IV_Y_V_20260912`), namespace
`Erdos81.RationalFarkas` → `PaperV.RationalFarkas`; no proof term changed. Re-gated in the Paper V build.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.Lift
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

/-!
# Farkas' lemma over the rationals, by Fourier--Motzkin elimination

This module is completely self contained: it proves, for a finite system of
rational linear inequalities

  `∀ j, ∑ k, M j k * x k ≤ b j`,

that either the system has a rational solution, or there is a nonnegative
rational certificate of infeasibility

  `y ≥ 0`, `∑ j, y j * M j k = 0` for every variable `k`, and `∑ j, y j * b j < 0`.

The proof is the classical Fourier--Motzkin elimination, by induction on the
number of variables: the last variable is eliminated by combining every
inequality having a positive coefficient with every inequality having a
negative coefficient, and both alternatives lift back.  No analysis, no
compactness and no real numbers are involved, so all produced data is rational.
-/

open scoped BigOperators

namespace FiniteLP.Rat

universe u v

variable {J : Type u} {N : Type v}

/-- The point `x` satisfies the finite system `M x ≤ b`. -/
def Sat [Fintype N] (M : J → N → ℚ) (b : J → ℚ) (x : N → ℚ) : Prop :=
  ∀ j, ∑ k, M j k * x k ≤ b j

/-- `y` is a Farkas certificate of infeasibility of `M x ≤ b`. -/
def Cert [Fintype J] [Fintype N] (M : J → N → ℚ) (b : J → ℚ) (y : J → ℚ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ (∀ k, ∑ j, y j * M j k = 0) ∧ ∑ j, y j * b j < 0

/-- A system cannot be both satisfiable and refutable. -/
theorem not_sat_of_cert [Fintype J] [Fintype N] {M : J → N → ℚ} {b : J → ℚ}
    {x : N → ℚ} {y : J → ℚ} (hx : Sat M b x) (hy : Cert M b y) : False := by
  obtain ⟨hy0, hyM, hyb⟩ := hy
  have h1 : ∑ j, y j * (∑ k, M j k * x k) ≤ ∑ j, y j * b j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (hy0 j)
  have h2 : ∑ j, y j * (∑ k, M j k * x k) = ∑ k, (∑ j, y j * M j k) * x k := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h2] at h1
  have h3 : ∑ k, (∑ j, y j * M j k) * x k = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hyM k, zero_mul]
  rw [h3] at h1
  linarith

/-- Splitting a `dite`-weighted sum over a decidable predicate into a sum over
the corresponding subtype. -/
theorem sum_dite_subtype {J : Type u} [Fintype J] (p : J → Prop) [DecidablePred p]
    (f : {j : J // p j} → ℚ) :
    ∑ j : J, (if h : p j then f ⟨j, h⟩ else 0) = ∑ j : {j : J // p j}, f j := by
  classical
  have h1 :
      ∑ j : J, (if h : p j then f ⟨j, h⟩ else 0)
        = ∑ j ∈ Finset.univ.filter p, (if h : p j then f ⟨j, h⟩ else 0) := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j _ hj
    by_contra hcon
    exact hj (dif_neg hcon)
  rw [h1, Finset.sum_subtype (p := p) (s := Finset.univ.filter p)
    (fun x => by simp) (f := fun j => if h : p j then f ⟨j, h⟩ else 0)]
  exact Finset.sum_congr rfl fun j _ => by simp [j.2]

/-- **Farkas' lemma / Fourier--Motzkin elimination over `ℚ`**, for variables
indexed by `Fin n`. -/
theorem fin_farkas :
    ∀ (n : ℕ) {J : Type u} [Fintype J] (M : J → Fin n → ℚ) (b : J → ℚ),
      (∃ x : Fin n → ℚ, Sat M b x) ∨ (∃ y : J → ℚ, Cert M b y) := by
  intro n
  induction n with
  | zero =>
      intro J _ M b
      by_cases hb : ∀ j, 0 ≤ b j
      · exact Or.inl ⟨fun k => k.elim0, by intro j; simpa using hb j⟩
      · push_neg at hb
        obtain ⟨j0, hj0⟩ := hb
        classical
        refine Or.inr ⟨fun j => if j = j0 then 1 else 0, ?_, ?_, ?_⟩
        · intro j; by_cases h : j = j0 <;> simp [h]
        · intro k; exact k.elim0
        · simpa using hj0
  | succ n ih =>
      intro J _ M b
      classical
      set a : J → ℚ := fun j => M j (Fin.last n) with ha
      set P : Type u := {j : J // 0 < a j} with hP
      set Q : Type u := {j : J // a j < 0} with hQ
      set Z : Type u := {j : J // a j = 0} with hZ
      set lift : (J → ℚ) → (Z ⊕ (P × Q)) → ℚ := fun f κ =>
        match κ with
        | Sum.inl j => f j.1
        | Sum.inr (p, q) => (-(a q.1)) * f p.1 + (a p.1) * f q.1
        with hlift
      set NN : (Z ⊕ (P × Q)) → Fin n → ℚ :=
        fun κ k => lift (fun j => M j k.castSucc) κ with hNN
      set cc : (Z ⊕ (P × Q)) → ℚ := lift b with hcc
      rcases ih NN cc with ⟨x, hx⟩ | ⟨z, hz0, hzk, hzb⟩
      · -- lift a solution of the reduced system
        left
        set S : J → ℚ := fun j => ∑ k : Fin n, M j k.castSucc * x k with hS
        have hz : ∀ j : Z, S j.1 ≤ b j.1 := by
          intro j
          have h := hx (Sum.inl j)
          simpa [hNN, hcc, hlift, hS] using h
        have hpair : ∀ (p : P) (q : Q),
            (-(a q.1)) * S p.1 + (a p.1) * S q.1
              ≤ (-(a q.1)) * b p.1 + (a p.1) * b q.1 := by
          intro p q
          have h := hx (Sum.inr (p, q))
          have hrw : ∑ k : Fin n, NN (Sum.inr (p, q)) k * x k
              = (-(a q.1)) * S p.1 + (a p.1) * S q.1 := by
            simp only [hNN, hlift, hS, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [hrw] at h
          simpa [hcc, hlift] using h
        set L : Q → ℚ := fun q => (S q.1 - b q.1) / (-(a q.1)) with hL
        set U : P → ℚ := fun p => (b p.1 - S p.1) / (a p.1) with hU
        have hLU : ∀ (p : P) (q : Q), L q ≤ U p := by
          intro p q
          have hp : 0 < a p.1 := p.2
          have hq : 0 < -(a q.1) := by have := q.2; linarith
          rw [hL, hU, div_le_div_iff₀ hq hp]
          nlinarith [hpair p q]
        set t : ℚ :=
          if hQne : (Finset.univ : Finset Q).Nonempty then
            Finset.univ.sup' hQne L
          else if hPne : (Finset.univ : Finset P).Nonempty then
            Finset.univ.inf' hPne U
          else 0 with ht
        have htQ : ∀ q : Q, L q ≤ t := by
          intro q
          have hQne : (Finset.univ : Finset Q).Nonempty := ⟨q, Finset.mem_univ q⟩
          rw [ht, dif_pos hQne]
          exact Finset.le_sup' L (Finset.mem_univ q)
        have htP : ∀ p : P, t ≤ U p := by
          intro p
          by_cases hQne : (Finset.univ : Finset Q).Nonempty
          · rw [ht, dif_pos hQne]
            exact Finset.sup'_le hQne L fun q _ => hLU p q
          · have hPne : (Finset.univ : Finset P).Nonempty := ⟨p, Finset.mem_univ p⟩
            rw [ht, dif_neg hQne, dif_pos hPne]
            exact Finset.inf'_le U (Finset.mem_univ p)
        refine ⟨Fin.snoc x t, ?_⟩
        intro j
        have hsum : ∑ k : Fin (n + 1), M j k * (Fin.snoc x t : Fin (n + 1) → ℚ) k
            = S j + a j * t := by
          rw [Fin.sum_univ_castSucc]
          simp [hS, ha]
        rw [hsum]
        rcases lt_trichotomy (a j) 0 with hj | hj | hj
        · have hqmem : L ⟨j, hj⟩ ≤ t := htQ ⟨j, hj⟩
          have hneg : 0 < -(a j) := by linarith
          rw [hL] at hqmem
          have hmul := (div_le_iff₀ hneg).mp hqmem
          nlinarith
        · have h := hz ⟨j, hj⟩
          rw [hj]
          simpa using h
        · have hpmem : t ≤ U ⟨j, hj⟩ := htP ⟨j, hj⟩
          rw [hU] at hpmem
          have hmul := (le_div_iff₀ hj).mp hpmem
          nlinarith
      · -- lift a certificate of the reduced system
        right
        set y : J → ℚ := fun j =>
          (if h : a j = 0 then z (Sum.inl ⟨j, h⟩) else 0)
          + (if h : 0 < a j then ∑ q : Q, z (Sum.inr (⟨j, h⟩, q)) * (-(a q.1)) else 0)
          + (if h : a j < 0 then ∑ p : P, z (Sum.inr (p, ⟨j, h⟩)) * (a p.1) else 0)
          with hy
        have key : ∀ f : J → ℚ, ∑ j, y j * f j = ∑ κ, z κ * lift f κ := by
          intro f
          have hexp : ∀ j : J, y j * f j
              = (if h : a j = 0 then z (Sum.inl ⟨j, h⟩) * f j else 0)
                + (if h : 0 < a j then
                    (∑ q : Q, z (Sum.inr (⟨j, h⟩, q)) * (-(a q.1))) * f j else 0)
                + (if h : a j < 0 then
                    (∑ p : P, z (Sum.inr (p, ⟨j, h⟩)) * (a p.1)) * f j else 0) := by
            intro j
            rw [hy]
            by_cases h1 : a j = 0 <;> by_cases h2 : 0 < a j <;> by_cases h3 : a j < 0 <;>
              simp [h1, h2, h3, add_mul]
          rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hexp j,
            Finset.sum_add_distrib, Finset.sum_add_distrib,
            sum_dite_subtype (p := fun j => a j = 0) (f := fun j => z (Sum.inl j) * f j.1),
            sum_dite_subtype (p := fun j => 0 < a j)
              (f := fun j => (∑ q : Q, z (Sum.inr (j, q)) * (-(a q.1))) * f j.1),
            sum_dite_subtype (p := fun j => a j < 0)
              (f := fun j => (∑ p : P, z (Sum.inr (p, j)) * (a p.1)) * f j.1),
            Fintype.sum_sum_type, Fintype.sum_prod_type]
          have hB : ∑ jp : P, (∑ q : Q, z (Sum.inr (jp, q)) * (-(a q.1))) * f jp.1
              = ∑ p : P, ∑ q : Q, z (Sum.inr (p, q)) * (-(a q.1)) * f p.1 :=
            Finset.sum_congr rfl fun p _ => Finset.sum_mul _ _ _
          have hC : ∑ jq : Q, (∑ p : P, z (Sum.inr (p, jq)) * (a p.1)) * f jq.1
              = ∑ p : P, ∑ q : Q, z (Sum.inr (p, q)) * (a p.1) * f q.1 := by
            rw [Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => Finset.sum_mul
              (Finset.univ : Finset P) (fun p => z (Sum.inr (p, q)) * (a p.1)) (f q.1)]
            exact Finset.sum_comm
          have hpairs :
              (∑ p : P, ∑ q : Q, z (Sum.inr (p, q)) * (-(a q.1)) * f p.1)
                + (∑ p : P, ∑ q : Q, z (Sum.inr (p, q)) * (a p.1) * f q.1)
              = ∑ p : P, ∑ q : Q, z (Sum.inr (p, q)) * lift f (Sum.inr (p, q)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun q _ => ?_
            show _ = z (Sum.inr (p, q)) * ((-(a q.1)) * f p.1 + (a p.1) * f q.1)
            ring
          rw [hB, hC, add_assoc, hpairs]
        refine ⟨y, ?_, ?_, ?_⟩
        · intro j
          have h1 : (0 : ℚ) ≤ if h : a j = 0 then z (Sum.inl ⟨j, h⟩) else 0 := by
            by_cases h : a j = 0
            · simp only [dif_pos h]; exact hz0 _
            · simp [h]
          have h2 : (0 : ℚ) ≤
              if h : 0 < a j then ∑ q : Q, z (Sum.inr (⟨j, h⟩, q)) * (-(a q.1)) else 0 := by
            by_cases h : 0 < a j
            · simp only [dif_pos h]
              refine Finset.sum_nonneg fun q _ => mul_nonneg (hz0 _) ?_
              have := q.2; linarith
            · simp [h]
          have h3 : (0 : ℚ) ≤
              if h : a j < 0 then ∑ p : P, z (Sum.inr (p, ⟨j, h⟩)) * (a p.1) else 0 := by
            by_cases h : a j < 0
            · simp only [dif_pos h]
              exact Finset.sum_nonneg fun p _ => mul_nonneg (hz0 _) (le_of_lt p.2)
            · simp [h]
          rw [hy]
          exact add_nonneg (add_nonneg h1 h2) h3
        · intro k
          refine Fin.lastCases ?_ ?_ k
          · have hzero : ∀ κ, z κ * lift a κ = 0 := by
              intro κ
              match κ with
              | Sum.inl j => simp [hlift, j.2]
              | Sum.inr (p, q) =>
                  have : lift a (Sum.inr (p, q)) = 0 := by simp [hlift]; ring
                  rw [this, mul_zero]
            have := key a
            rw [Finset.sum_congr rfl fun κ (_ : κ ∈ Finset.univ) => hzero κ] at this
            simpa [ha] using this.trans (Finset.sum_const_zero)
          · intro i
            have := key (fun j => M j i.castSucc)
            rw [this]
            have hzk' := hzk i
            calc ∑ κ, z κ * lift (fun j => M j i.castSucc) κ
                = ∑ κ, z κ * NN κ i := by
                  exact Finset.sum_congr rfl fun κ _ => by rw [hNN]
              _ = 0 := hzk'
        · rw [key b]
          calc ∑ κ, z κ * lift b κ = ∑ κ, z κ * cc κ := by
                exact Finset.sum_congr rfl fun κ _ => by rw [hcc]
            _ < 0 := hzb

/-- **Farkas' lemma over `ℚ`** for variables indexed by an arbitrary finite
type: a finite rational system either has a rational solution or a
nonnegative rational certificate of infeasibility. -/
theorem farkas {J : Type u} {N : Type v} [Fintype J] [Fintype N] (M : J → N → ℚ) (b : J → ℚ) :
    (∃ x : N → ℚ, Sat M b x) ∨ (∃ y : J → ℚ, Cert M b y) := by
  classical
  let e : N ≃ Fin (Fintype.card N) := Fintype.equivFin N
  rcases fin_farkas (Fintype.card N) (fun j k => M j (e.symm k)) b with ⟨x, hx⟩ | ⟨y, hy⟩
  · refine Or.inl ⟨fun n => x (e n), ?_⟩
    intro j
    have hsum : ∑ n : N, M j n * x (e n)
        = ∑ k : Fin (Fintype.card N), M j (e.symm k) * x k := by
      rw [← Equiv.sum_comp e.symm (fun n => M j n * x (e n))]
      exact Finset.sum_congr rfl fun k _ => by simp
    rw [hsum]
    exact hx j
  · refine Or.inr ⟨y, hy.1, ?_, hy.2.2⟩
    intro n
    have := hy.2.1 (e n)
    simpa using this

end FiniteLP.Rat
