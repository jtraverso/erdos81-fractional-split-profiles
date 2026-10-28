/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
  Finite linear-programming strong duality (covering / packing form).

  Self-contained development, `import Mathlib`.  The main export is
  `FiniteLP.covering_packing_duality`, a finite LP strong-duality theorem for a
  nonnegative incidence matrix `A` with nonnegative capacities `r`:

      max { ∑ t, w t : w ≥ 0, ∀ e, ∑ t A e t w t ≤ r e }
        =
      min { ∑ e, r e x e : x ≥ 0, ∀ t, ∑ e A e t x e ≥ 1 }

  and the maximum is attained.  It is proved from a finite Farkas lemma
  (`FiniteLP.farkas_ge`), which in turn rests on the closedness of a finitely
  generated cone (`FiniteLP.fg_cone_isClosed`) together with Mathlib's
  hyperplane-separation theorem for closed convex cones.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace FiniteLP

/-- The column vector `(N · j)` viewed as an element of `EuclideanSpace ℝ ι`. -/
noncomputable def col {ι κ : Type*} [Fintype ι] (N : ι → κ → ℝ) (j : κ) :
    EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => N i j)

/-- A generic vector of `EuclideanSpace ℝ ι` given by its coordinates. -/
noncomputable def toE {ι : Type*} [Fintype ι] (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm f

@[simp] lemma toE_apply {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) : toE f i = f i := rfl

lemma inner_toE {ι : Type*} [Fintype ι] (f : ι → ℝ) (y : EuclideanSpace ℝ ι) :
    (inner ℝ (toE f) y) = ∑ i, f i * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, toE, mul_comm]

/-! ### Closedness of a finitely generated cone -/

/-- A simplicial cone (nonnegative combinations of a linearly independent finite family) is
closed: it is the image of the closed nonnegative orthant under an injective (hence closed)
linear map. -/
lemma simplicial_cone_isClosed {κ ι : Type*} [Fintype κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (s : Finset κ) (hli : LinearIndepOn ℝ v s) :
    IsClosed {y : EuclideanSpace ℝ ι |
      ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
  classical
  set L : (s → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
    ∑ k : s, LinearMap.smulRight (LinearMap.proj k) (v k) with hL_def
  have hLval : ∀ c : s → ℝ, L c = ∑ k : s, c k • v k := by
    intro c
    simp [hL_def, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rw [hLval] at hm
    funext k; exact Fintype.linearIndependent_iff.mp hli m hm k
  have hclosedmap : IsClosedMap L :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot_of_injective hLinj)).isClosedMap
  have hO : IsClosed {c : s → ℝ | ∀ k, 0 ≤ c k} := by
    have : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext c; simp
    rw [this]
    exact isClosed_iInter (fun k => isClosed_le continuous_const (continuous_apply k))
  have hclosed := hclosedmap _ hO
  convert hclosed using 1
  ext y
  constructor
  · rintro ⟨c, hc0, hcoff, rfl⟩
    refine ⟨fun k : s => c k, fun k => hc0 _, ?_⟩
    rw [hLval, ← Finset.sum_attach s (fun j => c j • v j)]
    rfl
  · rintro ⟨c, hc0, rfl⟩
    refine ⟨fun j => if h : j ∈ s then c ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro k; dsimp only; split_ifs with h
      · exact hc0 _
      · exact le_refl 0
    · intro k hk; simp [hk]
    · rw [hLval, ← Finset.sum_attach s (fun j => (if h : j ∈ s then c ⟨j, h⟩ else 0) • v j)]
      apply Finset.sum_congr rfl
      intro k _
      simp [k.2]

/-
Conic Carathéodory: any nonnegative combination of a finite family can be rewritten as a
nonnegative combination of a linearly independent subfamily giving the same value.
-/
set_option maxHeartbeats 2000000 in
lemma conic_caratheodory {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∃ (d : κ → ℝ) (s : Finset κ), (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧
      LinearIndepOn ℝ v s ∧ (∑ k ∈ s, d k • v k) = ∑ k, c k • v k := by
  -- Among all finsets `s` and coefficient functions `d : κ → ℝ` with `d ≥ 0`, `d = 0` off `s`, and `∑ k ∈ s, d k • v k = ∑ k, c k • v k`, choose one whose support (as a finset) has minimal cardinality.
  obtain ⟨s, hs⟩ : ∃ s : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧ (∑ k ∈ s, d k • v k = ∑ k, c k • v k)) ∧ ∀ t : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ t, d k = 0) ∧ (∑ k ∈ t, d k • v k = ∑ k, c k • v k)) → s.card ≤ t.card := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.toFinite _;
    · exact ⟨ Finset.univ, ⟨ c, hc, fun k hk => False.elim <| hk <| Finset.mem_univ _, by simp +decide ⟩ ⟩;
  by_cases h_lin_dep : ¬ LinearIndepOn ℝ v s;
  · obtain ⟨d, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨a, ha_nonzero, ha_support, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) ∧ (∃ k ∈ s, a k > 0) := by
      obtain ⟨a, ha_nonzero, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) := by
        rw [ linearIndepOn_iff' ] at h_lin_dep;
        push Not at h_lin_dep;
        obtain ⟨ t, g, ht, hg, i, hi, hi' ⟩ := h_lin_dep; use fun k => if k ∈ t then g k else 0; simp_all +decide [ Finset.sum_ite ] ;
        exact ⟨ ⟨ i, ht hi, hi, hi' ⟩, fun k hk₁ hk₂ => False.elim <| hk₁ <| ht hk₂, by rw [ Finset.inter_eq_right.mpr ht, hg ] ⟩;
      by_cases h_neg : ∀ k ∈ s, a k ≤ 0;
      · use fun k => -a k;
        simp_all +decide [ neg_smul ];
        exact ha_nonzero.imp fun k hk => ⟨ hk.1, lt_of_le_of_ne ( h_neg k hk.1 ) hk.2 ⟩;
      · exact ⟨ a, ha_nonzero, ha_sum.1, ha_sum.2, by push Not at h_neg; exact h_neg ⟩;
    -- Choose $\theta > 0$ such that $d - \theta a$ is nonnegative and supported on a strictly smaller set than $s$.
    obtain ⟨θ, hθ_pos, hθ_min⟩ : ∃ θ > 0, (∀ k ∈ s, d k - θ * a k ≥ 0) ∧ (∃ k ∈ s, d k - θ * a k = 0) := by
      -- Choose $\theta$ to be the minimum of $d_k / a_k$ over all $k \in s$ where $a_k > 0$.
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ ∈ s, a k₀ > 0 ∧ ∀ k ∈ s, a k > 0 → d k / a k ≥ d k₀ / a k₀ := by
        have h_min : ∃ k₀ ∈ Finset.filter (fun k => a k > 0) s, ∀ k ∈ Finset.filter (fun k => a k > 0) s, d k / a k ≥ d k₀ / a k₀ := by
          exact Finset.exists_min_image _ _ ⟨ ha_sum.2.choose, Finset.mem_filter.mpr ⟨ ha_sum.2.choose_spec.1, ha_sum.2.choose_spec.2 ⟩ ⟩;
        exact ⟨ h_min.choose, Finset.mem_filter.mp h_min.choose_spec.1 |>.1, Finset.mem_filter.mp h_min.choose_spec.1 |>.2, fun k hk hk' => h_min.choose_spec.2 k ( Finset.mem_filter.mpr ⟨ hk, hk' ⟩ ) ⟩;
      refine' ⟨ d k₀ / a k₀, div_pos ( lt_of_le_of_ne ( hd_nonneg k₀ ) ( Ne.symm _ ) ) hk₀.2.1, _, k₀, hk₀.1, _ ⟩;
      · intro h; simp_all +decide;
        have := hs.2 ( s.erase k₀ ) ( fun k => if k = k₀ then 0 else d k ) ?_ ?_ ?_
        · rw [Finset.card_erase_of_mem hk₀.1] at this
          have := Finset.card_pos.mpr ⟨k₀, hk₀.1⟩
          omega
        · intro k; split_ifs <;> simp [hd_nonneg]
        · intro k hk
          split_ifs with h'
          · rfl
          · simp only [Finset.mem_erase, h', ne_eq, not_false_eq_true, true_and] at hk
            exact hd_zero k hk
        · have hcongr : ∀ k ∈ s.erase k₀, (if k = k₀ then 0 else d k) • v k = d k • v k :=
            fun k hk => by simp [Finset.ne_of_mem_erase hk]
          rw [Finset.sum_congr rfl hcongr, Finset.sum_erase _ (by simp [h])]
          exact hd_sum
      · intro k hk; by_cases hk' : a k > 0 <;> simp_all +decide;
        · exact le_div_iff₀ hk' |>.1 ( hk₀.2.2 k hk hk' );
        · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( div_nonneg ( hd_nonneg _ ) hk₀.2.1.le ) hk' ) ( hd_nonneg _ );
      · rw [ div_mul_cancel₀ _ hk₀.2.1.ne', sub_self ];
    -- Let $t = s.filter (fun k => d k - θ * a k ≠ 0)$ be the support of $d - θ a$.
    set t := s.filter (fun k => d k - θ * a k ≠ 0) with ht_def;
    -- Then $d - \theta a$ is nonnegative, supported on $t$, and $\sum_{k \in t} (d k - \theta a k) • v k = \sum_{k \in s} d k • v k$.
    have h_t_support : ∀ k, 0 ≤ d k - θ * a k := by
      exact fun k => if hk : k ∈ s then hθ_min.1 k hk else by simp +decide [ hd_zero k hk, ha_support k hk ] ;
    have h_t_zero : ∀ k ∉ t, d k - θ * a k = 0 := by
      grind
    have h_t_sum : ∑ k ∈ t, (d k - θ * a k) • v k = ∑ k, c k • v k := by
      convert congr_arg ( fun x => x - θ • ∑ k ∈ s, a k • v k ) hd_sum using 1;
      · rw [ Finset.sum_filter_of_ne ];
        · simp +decide [ sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul ];
        · exact fun k hk hk' => fun hk'' => hk' <| by rw [ hk'', zero_smul ] ;
      · simp +decide [ ha_sum.1 ];
    contrapose! hs;
    refine' fun h => ⟨ t, ⟨ fun k => d k - θ * a k, h_t_support, h_t_zero, h_t_sum ⟩, _ ⟩;
    refine' Finset.card_lt_card _;
    grind;
  · exact ⟨ hs.1.choose, s, hs.1.choose_spec.1, hs.1.choose_spec.2.1, Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2 ⟩

/-- The finitely generated cone `{∑ k c k • v k : c ≥ 0}` is closed. -/
lemma fg_cone_isClosed {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) :
    IsClosed {y : EuclideanSpace ℝ ι | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y} := by
  have hset : {y : EuclideanSpace ℝ ι | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y}
      = ⋃ s : Finset κ, ⋃ (_ : LinearIndepOn ℝ v s),
          {y : EuclideanSpace ℝ ι |
            ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc0, rfl⟩
      obtain ⟨d, s, hd0, hdoff, hindep, hsum⟩ := conic_caratheodory v c hc0
      exact ⟨s, hindep, d, hd0, hdoff, hsum⟩
    · rintro ⟨s, hindep, c, hc0, hcoff, rfl⟩
      refine ⟨c, hc0, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      intro k _ hks; rw [hcoff k hks, zero_smul]
  rw [hset]
  exact isClosed_iUnion_of_finite fun s =>
    isClosed_iUnion_of_finite fun h => simplicial_cone_isClosed v s h

/-! ### Finite Farkas lemma -/

/-- **Finite Farkas lemma (inequality form).**  If the primal system
`x ≥ 0, N x ≥ c` is infeasible, then there is a Farkas certificate `y ≥ 0` with
`Nᵀ y ≤ 0` and `⟨c, y⟩ > 0`. -/
theorem farkas_ge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ι → κ → ℝ) (c : ι → ℝ)
    (hinfeas : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, N i j * y i ≤ 0) ∧ 0 < ∑ i, c i * y i := by
  classical
  set g : (κ ⊕ ι) → EuclideanSpace ℝ ι :=
    Sum.elim (fun j => toE (fun i => N i j)) (fun i => toE (fun i' => if i' = i then (-1:ℝ) else 0)) with hg
  have hind : ∀ a : κ ⊕ ι, ∑ k, (if k = a then (1:ℝ) else 0) • g k = g a := by
    intro a; simp [ite_smul]
  set S : Set (EuclideanSpace ℝ ι) := {y | ∃ coeff : (κ ⊕ ι) → ℝ, (∀ k, 0 ≤ coeff k) ∧ ∑ k, coeff k • g k = y} with hS
  have hSclosed : IsClosed S := fg_cone_isClosed g
  let K : ProperCone ℝ (EuclideanSpace ℝ ι) :=
    { carrier := S
      zero_mem' := ⟨fun _ => 0, fun _ => le_refl 0, by simp⟩
      smul_mem' := by
        rintro t x ⟨coeff, hcoeff, rfl⟩
        exact ⟨fun k => (t : ℝ) * coeff k, fun k => mul_nonneg t.2 (hcoeff k), by
          rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _
          rw [← smul_smul]; rfl⟩
      add_mem' := by
        rintro x y ⟨c1, h1, rfl⟩ ⟨c2, h2, rfl⟩
        exact ⟨fun k => c1 k + c2 k, fun k => add_nonneg (h1 k) (h2 k), by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; rw [add_smul]⟩
      isClosed' := hSclosed }
  have hcne : (toE c) ∉ K := by
    rintro ⟨coeff, hcoeff, hsum⟩
    apply hinfeas
    refine ⟨fun j => coeff (Sum.inl j), fun j => hcoeff _, ?_⟩
    intro i
    have hcoord := congrArg (fun z => z i) hsum
    simp only [toE_apply] at hcoord
    have hexp : (∑ k, coeff k • g k) i
        = (∑ j, coeff (Sum.inl j) * N i j) - coeff (Sum.inr i) := by
      rw [Fintype.sum_sum_type]
      simp [hg, EuclideanSpace, PiLp, Finset.sum_apply]
      ring
    have hcomm : ∑ j, N i j * coeff (Sum.inl j) = ∑ j, coeff (Sum.inl j) * N i j := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hexp] at hcoord
    have hnn : 0 ≤ coeff (Sum.inr i) := hcoeff _
    linarith
  obtain ⟨y, hy1, hy2⟩ :=
    ProperCone.hyperplane_separation' K hcne
  refine ⟨fun i => -(y i), fun i => ?_, fun j => ?_, ?_⟩
  · have hmem : g (Sum.inr i) ∈ K := ⟨fun k => if k = Sum.inr i then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inr] at hh
    rw [inner_toE] at hh
    have hval : ∑ i', (if i' = i then (-1:ℝ) else 0) * y i' = - y i := by
      rw [Finset.sum_eq_single i] <;> simp +contextual
    rw [hval] at hh
    change 0 ≤ - y i; linarith
  · have hmem : g (Sum.inl j) ∈ K := ⟨fun k => if k = Sum.inl j then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inl] at hh
    rw [inner_toE] at hh
    have h2 : ∑ i, N i j * -(y i) = - ∑ i, (fun i => N i j) i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith
  · rw [inner_toE] at hy2
    have h2 : ∑ i, c i * -(y i) = - ∑ i, c i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith

/-! ### Strong duality -/

/-
**Finite LP strong duality (covering/packing).**  For a nonnegative incidence matrix `A`
with nonnegative capacities `r`, in which every column has a positive entry, there is a maximum
packing `w` whose value equals the covering optimum.
-/
theorem covering_packing_duality
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (r : ι → ℝ)
    (hA : ∀ e t, 0 ≤ A e t) (hr : ∀ e, 0 ≤ r e)
    (hcol : ∀ t, ∃ e, 0 < A e t) :
    ∃ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, (∑ t, A e t * w t) ≤ r e) ∧
      (∑ t, w t) = sInf {v : ℝ | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
        (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
  by_contra h_no_wstar;
  -- By definition of $P$, we know that for any $w \in Q$, $\sum t, w t \leq Mr$.
  have hP_le_Mr : ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    intro w hw;
    refine' le_csInf _ _;
    · refine' ⟨ _, ⟨ fun e => ∑ t, 1 / A e t, _, _, rfl ⟩ ⟩;
      · exact fun e => Finset.sum_nonneg fun t _ => one_div_nonneg.2 ( hA e t );
      · intro t; obtain ⟨ e, he ⟩ := hcol t; refine' le_trans _ ( Finset.single_le_sum ( fun e _ => mul_nonneg ( hA e t ) ( Finset.sum_nonneg fun t _ => one_div_nonneg.mpr ( hA e t ) ) ) ( Finset.mem_univ e ) ) ; simp +decide [ he.ne', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
        exact le_trans ( by norm_num [ he.ne' ] ) ( Finset.single_le_sum ( fun i _ => mul_nonneg he.le ( inv_nonneg.2 ( hA e i ) ) ) ( Finset.mem_univ t ) );
    · rintro _ ⟨ x, hx₁, hx₂, rfl ⟩;
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ t, w t * (∑ e, A e t * x e) = ∑ e, (∑ t, A e t * w t) * x e := by
        simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using Finset.sum_comm;
      exact le_trans ( Finset.sum_le_sum fun t _ => le_mul_of_one_le_right ( hw.1 t ) ( hx₂ t ) ) ( h_fubini.le.trans ( Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right ( hw.2 e ) ( hx₁ e ) ) );
  -- By definition of $P$, we know that there exists a maximum packing $w^* \in Q$ such that $\sum t, w^* t = P$.
  obtain ⟨w_star, hw_star⟩ : ∃ w_star : κ → ℝ, (∀ t, 0 ≤ w_star t) ∧ (∀ e, ∑ t, A e t * w_star t ≤ r e) ∧ ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ ∑ t, w_star t := by
    have h_compact : IsCompact {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)} := by
      refine' CompactIccSpace.isCompact_Icc.of_isClosed_subset _ _;
      exact fun t => 0;
      exact fun t => sInf { v | ∃ x : ι → ℝ, ( ∀ e, 0 ≤ x e ) ∧ ( ∀ t, 1 ≤ ∑ e, A e t * x e ) ∧ v = ∑ e, r e * x e };
      · simp +decide only [Set.ofPred_and, Set.ofPred_forall];
        exact IsClosed.inter ( isClosed_iInter fun _ => isClosed_le continuous_const <| continuous_apply _ ) ( isClosed_iInter fun _ => isClosed_le ( continuous_finsetSum _ fun _ _ => continuous_const.mul <| continuous_apply _ ) continuous_const );
      · exact fun w hw => ⟨ hw.1, fun t => le_trans ( Finset.single_le_sum ( fun a _ => hw.1 a ) ( Finset.mem_univ t ) ) ( hP_le_Mr w hw ) ⟩;
    have h_nonempty : {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)}.Nonempty := by
      exact ⟨ fun _ => 0, fun _ => le_rfl, fun _ => by simp +decide [ hr ] ⟩;
    have := h_compact.exists_isMaxOn h_nonempty ( show ContinuousOn ( fun w : κ → ℝ => ∑ t, w t ) _ from Continuous.continuousOn <| continuous_finsetSum _ fun _ _ => continuous_apply _ );
    exact ⟨ this.choose, this.choose_spec.1.1, this.choose_spec.1.2, fun w hw => this.choose_spec.2 hw ⟩;
  -- By definition of $P$, we know that $P < Mr$.
  have hP_lt_Mr : ∑ t, w_star t < sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    exact lt_of_le_of_ne ( hP_le_Mr w_star ⟨ hw_star.1, hw_star.2.1 ⟩ ) fun h => h_no_wstar ⟨ w_star, hw_star.1, hw_star.2.1, h ⟩;
  -- By definition of $P$, we know that there exists a Farkas certificate $y$ such that $y \geq 0$, $\sum_{e} N'_{ie} y_i \leq 0$ for all $e$, and $\sum_{i} c'_i y_i > 0$.
  obtain ⟨y, hy_nonneg, hy_row, hy_obj⟩ : ∃ y : κ ⊕ Unit → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ e, ∑ i, (Sum.elim (fun t e => A e t) (fun _ e => -r e) i e) * y i ≤ 0) ∧ 0 < ∑ i, (Sum.elim (fun _ => 1) (fun _ => -∑ t, w_star t) i) * y i := by
    have h_farkas : ¬∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ ∑ e, r e * x e ≤ ∑ t, w_star t := by
      contrapose! hP_lt_Mr;
      exact le_trans ( csInf_le ⟨ 0, by rintro v ⟨ x, hx₁, hx₂, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hr _ ) ( hx₁ _ ) ⟩ ⟨ hP_lt_Mr.choose, hP_lt_Mr.choose_spec.1, hP_lt_Mr.choose_spec.2.1, rfl ⟩ ) hP_lt_Mr.choose_spec.2.2;
    convert farkas_ge ( fun i e => Sum.elim ( fun t e => A e t ) ( fun _ e => -r e ) i e ) ( fun i => Sum.elim ( fun _ => 1 ) ( fun _ => -∑ t, w_star t ) i ) _ using 1;
    simp +zetaDelta at *;
    exact h_farkas;
  -- Let $lam t = y (Sum.inl t)$ and $mu = y (Sum.inr ())$.
  set lam : κ → ℝ := fun t => y (Sum.inl t)
  set mu : ℝ := y (Sum.inr ());
  -- By definition of $lam$ and $mu$, we have $\sum_{t} A_{et} lam_t \leq mu r_e$ for all $e$ and $\sum_{t} lam_t > mu P$.
  have hlam_mu : ∀ e, ∑ t, A e t * lam t ≤ mu * r e := by
    intro e; specialize hy_row e; simp +decide [ Finset.sum_add_distrib, mul_comm ] at hy_row ⊢;
    exact hy_row
  have hlam_mu_P : ∑ t, lam t > mu * ∑ t, w_star t := by
    simp +zetaDelta at *;
    linarith;
  -- If $mu = 0$, then from $hlam_mu$, we have $\sum_{t} A_{et} lam_t \leq 0$ for all $e$, which implies $lam_t = 0$ for all $t$.
  by_cases hmu_zero : mu = 0;
  · simp +zetaDelta at *;
    simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_nonneg ];
    exact hy_obj.ne' ( Finset.sum_eq_zero fun t ht => le_antisymm ( le_of_not_gt fun h => by have := hy_row ( Classical.choose ( hcol t ) ) ; exact not_le_of_gt ( lt_of_lt_of_le ( mul_pos ( Classical.choose_spec ( hcol t ) ) h ) ( Finset.single_le_sum ( fun a _ => mul_nonneg ( hA _ a ) ( hy_nonneg a ) ) ht ) ) this ) ( hy_nonneg t ) );
  · -- Since $mu > 0$, we can divide both sides of $hlam_mu$ by $mu$ to get $\sum_{t} A_{et} (lam_t / mu) \leq r_e$ for all $e$.
    have hlam_mu_div : ∀ e, ∑ t, A e t * (lam t / mu) ≤ r e := by
      simp +decide only [← mul_div_assoc, ← sum_div];
      exact fun e => div_le_iff₀' ( lt_of_le_of_ne ( hy_nonneg _ ) ( Ne.symm hmu_zero ) ) |>.2 ( hlam_mu e );
    -- Since $mu > 0$, we can divide both sides of $hlam_mu_P$ by $mu$ to get $\sum_{t} (lam_t / mu) > \sum_{t} w_star t$.
    have hlam_mu_div_P : ∑ t, (lam t / mu) > ∑ t, w_star t := by
      rw [ ← Finset.sum_div _ _ _, gt_iff_lt, lt_div_iff₀ ] <;> cases lt_or_gt_of_ne hmu_zero <;> nlinarith [ hy_nonneg ( Sum.inr () ) ];
    exact not_le_of_gt hlam_mu_div_P ( hw_star.2.2 _ ⟨ fun t => div_nonneg ( hy_nonneg _ ) ( hy_nonneg _ ), hlam_mu_div ⟩ )

end FiniteLP