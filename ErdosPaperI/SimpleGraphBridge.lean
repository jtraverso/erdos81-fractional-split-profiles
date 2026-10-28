/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import ErdosPaperI.Sharp

/-!
# Paper I on Mathlib's `SimpleGraph`

The definitions of split graphs and of fractional triangle packings/covers of the author's
registered entries `jtraverso/chordal-split-threshold-graphs` and
`jtraverso/asymptotic-triangle-packing` (copied verbatim), and the bridge to the finite split
model `PaperI.Split`:

* `PaperI.fracCoverNumber_eq_fracPackingNumber`: `τ₃*(G) = ν₃*(G)` for every finite graph, from
  the finite LP duality `FiniteLP.covering_packing_duality`;
* `PaperI.Split.ofEquiv`: the split model of a graph whose vertex type is identified with
  `Fin p ⊕ Fin m` (clique part first, independent part second), with
  `edgeCount = |E(G)|`, `n = |V|` and `nu3star = ν₃*(G)`;
* `PaperI.split_main`, `PaperI.split_main_cover`: Paper I's sharp bound on `SimpleGraph`.
-/

@[expose] public section

namespace PaperI
open scoped BigOperators
open Classical Finset

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

def IsFracTriangleCover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (y : Sym2 V → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ ∀ t ∈ G.cliqueFinset 3, 1 ≤ ∑ e ∈ edgesIn G t, y e

/-- The fractional triangle packing number `ν₃*(G)`. -/
noncomputable def fracPackingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  sSup {s | ∃ w, IsFracTrianglePacking G w ∧ s = ∑ t ∈ G.cliqueFinset 3, w t}

/-- The fractional triangle cover number `τ₃*(G)`. -/
noncomputable def fracCoverNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  sInf {s | ∃ y : Sym2 V → ℝ, IsFracTriangleCover G y ∧ s = ∑ e, y e}


section General

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every triangle of `G` contains an edge of `G`. -/
theorem exists_mem_edgesIn {t : Finset V} (ht : t ∈ G.cliqueFinset 3) :
    ∃ e, e ∈ edgesIn G t := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, -, -, rfl⟩ := ht
  refine ⟨s(a, b), ?_⟩
  simp only [edgesIn, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  refine ⟨hab, fun v hv => ?_⟩
  rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp

/-- Weak duality: every packing value is at most every cover value. -/
theorem packing_le_cover {w : Finset V → ℝ} {y : Sym2 V → ℝ} (hw : IsFracTrianglePacking G w)
    (hy : IsFracTriangleCover G y) : ∑ t ∈ G.cliqueFinset 3, w t ≤ ∑ e, y e := by
  calc ∑ t ∈ G.cliqueFinset 3, w t
      ≤ ∑ t ∈ G.cliqueFinset 3, w t * ∑ e ∈ edgesIn G t, y e :=
        sum_le_sum fun t ht => le_mul_of_one_le_right (hw.1 t) (hy.2 t ht)
    _ = ∑ t ∈ G.cliqueFinset 3, ∑ e ∈ edgesIn G t, w t * y e := by simp only [mul_sum]
    _ = ∑ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t * y e := by
        refine Finset.sum_comm' fun t e => ?_
        simp only [mem_filter]
        constructor
        · rintro ⟨ht, he⟩
          exact ⟨⟨ht, he⟩, (mem_filter.mp he).1⟩
        · rintro ⟨⟨ht, he⟩, -⟩
          exact ⟨ht, he⟩
    _ = ∑ e ∈ G.edgeFinset, (∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t) * y e := by
        simp only [sum_mul]
    _ ≤ ∑ e ∈ G.edgeFinset, y e :=
        sum_le_sum fun e he => mul_le_of_le_one_left (hy.1 e) (hw.2 e he)
    _ ≤ ∑ e, y e := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun e _ _ => hy.1 e

theorem isFracTriangleCover_one : IsFracTriangleCover G (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun t ht => ?_⟩
  obtain ⟨e, he⟩ := exists_mem_edgesIn G ht
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.one_le_cast]
  exact card_pos.mpr ⟨e, he⟩

theorem isFracTrianglePacking_zero : IsFracTrianglePacking G (fun _ => 0) :=
  ⟨fun _ => le_rfl, fun _ _ => by simp⟩

/-- Strong duality: `τ₃*(G) = ν₃*(G)`. -/
theorem fracCoverNumber_eq_fracPackingNumber : fracCoverNumber G = fracPackingNumber G := by
  set A : G.edgeFinset → G.cliqueFinset 3 → ℝ :=
    fun e t => if (e : Sym2 V) ∈ edgesIn G t then 1 else 0 with hA
  have hA0 : ∀ e t, 0 ≤ A e t := fun e t => by simp only [hA]; split_ifs <;> norm_num
  have hcol : ∀ t, ∃ e, 0 < A e t := by
    intro t
    obtain ⟨e, he⟩ := exists_mem_edgesIn G t.2
    exact ⟨⟨e, (mem_filter.mp he).1⟩, by simp [hA, he]⟩
  obtain ⟨w0, hw0, hload, hval⟩ := FiniteLP.covering_packing_duality A (fun _ => 1) hA0
    (fun _ => zero_le_one) hcol
  set S0 := {v : ℝ | ∃ x : G.edgeFinset → ℝ, (∀ e, 0 ≤ x e) ∧
    (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, (fun _ => (1 : ℝ)) e * x e} with hS0
  set W : Finset V → ℝ := fun t => if h : t ∈ G.cliqueFinset 3 then w0 ⟨t, h⟩ else 0 with hW
  have hWval : ∑ t ∈ G.cliqueFinset 3, W t = ∑ t, w0 t := by
    rw [← Finset.sum_coe_sort]
    exact sum_congr rfl fun t _ => by simp only [hW]; rw [dite_eq_left t.2]
  have hWpack : IsFracTrianglePacking G W := by
    refine ⟨fun t => ?_, fun e he => ?_⟩
    · simp only [hW]; split_ifs <;> simp [hw0]
    · refine le_trans (le_of_eq ?_) (hload ⟨e, he⟩)
      rw [sum_filter, ← Finset.sum_coe_sort]
      refine sum_congr rfl fun t _ => ?_
      simp only [hA, hW, dite_eq_left t.2]
      split_ifs <;> simp
  have hS0ne : S0.Nonempty := by
    refine ⟨_, fun _ => 1, fun _ => zero_le_one, fun t => ?_, rfl⟩
    obtain ⟨e, he⟩ := hcol t
    refine le_trans ?_ (single_le_sum (fun e _ => mul_nonneg (hA0 e t) zero_le_one)
      (mem_univ e))
    have : A e t = 1 := by
      simp only [hA] at he ⊢; split_ifs at he ⊢ <;> simp_all
    simp [this]
  have hcover : fracCoverNumber G = ∑ t, w0 t := by
    refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt
      ⟨_, fun _ => 1, isFracTriangleCover_one G, rfl⟩ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [← hWval]
      exact packing_le_cover G hWpack hy
    · intro b hb
      rw [hval] at hb
      obtain ⟨_, ⟨x, hx0, hxcov, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hS0ne hb
      set y : Sym2 V → ℝ := fun e => if h : e ∈ G.edgeFinset then x ⟨e, h⟩ else 0 with hy
      have hyval : ∑ e, y e = ∑ e, x e := by
        rw [← sum_subset (subset_univ G.edgeFinset) fun e _ he => by
            simp only [hy]; rw [dite_eq_right he], ← Finset.sum_coe_sort]
        exact sum_congr rfl fun e _ => by simp only [hy]; rw [dite_eq_left e.2]
      refine ⟨∑ e, y e, ⟨y, ⟨fun e => ?_, fun t ht => ?_⟩, rfl⟩, ?_⟩
      · simp only [hy]; split_ifs <;> simp [hx0]
      · refine le_trans (hxcov ⟨t, ht⟩) (le_of_eq ?_)
        have hsub : edgesIn G t ⊆ G.edgeFinset := filter_subset _ _
        have hsum : ∑ e ∈ edgesIn G t, y e =
            ∑ e ∈ G.edgeFinset, if e ∈ edgesIn G t then y e else 0 := by
          rw [sum_ite_mem, inter_eq_right.mpr hsub]
        rw [hsum, ← Finset.sum_coe_sort G.edgeFinset]
        refine sum_congr rfl fun e _ => ?_
        simp only [hA, hy, dite_eq_left e.2]
        split_ifs <;> simp
      · simpa [hyval] using hlt
  rw [hcover]
  have hgr : IsGreatest {s | ∃ w, IsFracTrianglePacking G w ∧
      s = ∑ t ∈ G.cliqueFinset 3, w t} (∑ t, w0 t) := by
    refine ⟨⟨W, hWpack, hWval.symm⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← hcover]
    refine le_csInf ⟨_, fun _ => 1, isFracTriangleCover_one G, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    exact packing_le_cover G hw hy
  exact hgr.csSup_eq.symm

/-- Every packing value is at most `ν₃*(G)`. -/
theorem le_fracPackingNumber {w : Finset V → ℝ} (hw : IsFracTrianglePacking G w) :
    ∑ t ∈ G.cliqueFinset 3, w t ≤ fracPackingNumber G :=
  le_csSup ⟨∑ e : Sym2 V, (fun _ => (1 : ℝ)) e, by
    rintro _ ⟨w', hw', rfl⟩
    exact packing_le_cover G hw' (isFracTriangleCover_one G)⟩ ⟨w, hw, rfl⟩

end General

/-! ### The split model of a split graph -/

section Model

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {p m : ℕ} (E : Fin p ⊕ Fin m ≃ V)

/-- The split model of `G` with respect to an identification `E : Fin p ⊕ Fin m ≃ V`
(clique part `Fin p`, independent part `Fin m`): the neighbourhood of the independent
vertex `v` is the set of clique vertices adjacent to it. -/
abbrev Split.ofEquiv : Split where
  p := p
  ι := Fin m
  fι := inferInstance
  N v := Finset.univ.filter fun x => G.Adj (E (Sum.inr v)) (E (Sum.inl x))

/-- The edge of `G` corresponding to an edge of the split model. -/
def Split.ofEquiv.edgeMap : (Split.ofEquiv G E).Edge → Sym2 V
  | Sum.inl e => s(E (Sum.inl e.1.1), E (Sum.inl e.1.2))
  | Sum.inr e => s(E (Sum.inr e.1.1), E (Sum.inl e.1.2))

/-- The triangle of `G` corresponding to a triangle of the split model. -/
def Split.ofEquiv.triMap : (Split.ofEquiv G E).Triangle → Finset V
  | Sum.inl t => {E (Sum.inl t.1.1), E (Sum.inl t.1.2.1), E (Sum.inl t.1.2.2)}
  | Sum.inr t => {E (Sum.inr t.1.1), E (Sum.inl t.1.2.1), E (Sum.inl t.1.2.2)}

variable {G E}
variable (hcl : ∀ i j : Fin p, i ≠ j → G.Adj (E (Sum.inl i)) (E (Sum.inl j)))
variable (hind : ∀ a b : Fin m, ¬ G.Adj (E (Sum.inr a)) (E (Sum.inr b)))

namespace Split.ofEquiv

omit [Fintype V] [DecidableEq V] in
theorem E_inl_eq_iff (i j : Fin p) : E (Sum.inl i) = E (Sum.inl j) ↔ i = j := by
  rw [E.injective.eq_iff, Sum.inl.injEq]

omit [Fintype V] [DecidableEq V] in
theorem E_inr_eq_iff (v w : Fin m) : E (Sum.inr v) = E (Sum.inr w) ↔ v = w := by
  rw [E.injective.eq_iff, Sum.inr.injEq]

omit [Fintype V] [DecidableEq V] in
theorem E_inl_eq_inr_iff (i : Fin p) (v : Fin m) : E (Sum.inl i) = E (Sum.inr v) ↔ False := by
  rw [E.injective.eq_iff]; simp

omit [Fintype V] [DecidableEq V] in
theorem E_inr_eq_inl_iff (i : Fin p) (v : Fin m) : E (Sum.inr v) = E (Sum.inl i) ↔ False := by
  rw [E.injective.eq_iff]; simp

omit [DecidableEq V] in
include hcl in
theorem edgeMap_mem (e : (Split.ofEquiv G E).Edge) : edgeMap G E e ∈ G.edgeFinset := by
  rcases e with ⟨⟨i, j⟩, h⟩ | ⟨⟨v, x⟩, h⟩
  · exact SimpleGraph.mem_edgeFinset.mpr (hcl i j (ne_of_lt h))
  · exact SimpleGraph.mem_edgeFinset.mpr (mem_filter.mp h).2

omit [Fintype V] [DecidableEq V] in
theorem edgeMap_injective : Function.Injective (edgeMap G E) := by
  rintro (⟨⟨i, j⟩, h⟩ | ⟨⟨v, x⟩, h⟩) (⟨⟨i', j'⟩, h'⟩ | ⟨⟨v', x'⟩, h'⟩) heq <;>
    simp only [edgeMap, Sym2.eq_iff, E.injective.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, false_and, and_false, or_false, or_self] at heq
  · rcases heq with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩
    · rfl
    · exact absurd (h.trans h') (lt_irrefl _)
  · obtain ⟨⟨⟩, ⟨⟩⟩ := heq
    rfl

omit [DecidableEq V] in
include hind in
theorem edgeMap_surj {e : Sym2 V} (he : e ∈ G.edgeFinset) : ∃ e₀, edgeMap G E e₀ = e := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab : G.Adj a b := SimpleGraph.mem_edgeFinset.mp he
  obtain ⟨sa, rfl⟩ := E.surjective a
  obtain ⟨sb, rfl⟩ := E.surjective b
  rcases sa with i | v <;> rcases sb with j | w
  · have hij : i ≠ j := fun h => hab.ne (by rw [h])
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨Sum.inl ⟨(i, j), h⟩, rfl⟩
    · exact ⟨Sum.inl ⟨(j, i), h⟩, Sym2.eq_swap⟩
  · exact ⟨Sum.inr ⟨(w, i), mem_filter.mpr ⟨mem_univ _, hab.symm⟩⟩, Sym2.eq_swap⟩
  · exact ⟨Sum.inr ⟨(v, j), mem_filter.mpr ⟨mem_univ _, hab⟩⟩, rfl⟩
  · exact absurd hab (hind v w)

include hcl in
theorem triMap_mem (T : (Split.ofEquiv G E).Triangle) : triMap G E T ∈ G.cliqueFinset 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff]
  rcases T with ⟨⟨a, b, c⟩, hab, hbc⟩ | ⟨⟨v, x, y⟩, hxy, hx, hy⟩
  · exact SimpleGraph.is3Clique_triple_iff.mpr
      ⟨hcl a b (ne_of_lt hab), hcl a c (ne_of_lt (hab.trans hbc)), hcl b c (ne_of_lt hbc)⟩
  · exact SimpleGraph.is3Clique_triple_iff.mpr
      ⟨(mem_filter.mp hx).2, (mem_filter.mp hy).2, hcl x y (ne_of_lt hxy)⟩

omit [Fintype V] in
theorem triMap_injective : Function.Injective (triMap G E) := by
  rintro (⟨⟨a, b, c⟩, h⟩ | ⟨⟨v, x, y⟩, h⟩) (⟨⟨a', b', c'⟩, h'⟩ | ⟨⟨v', x', y'⟩, h'⟩) heq <;>
    have hm := Finset.ext_iff.mp heq <;>
    simp only [triMap, mem_insert, mem_singleton] at hm
  · have h1 := hm (E (Sum.inl a)); have h2 := hm (E (Sum.inl b)); have h3 := hm (E (Sum.inl c))
    have h4 := hm (E (Sum.inl a')); have h5 := hm (E (Sum.inl b'))
    have h6 := hm (E (Sum.inl c'))
    simp only [E_inl_eq_iff, true_or, or_true, true_iff, iff_true] at h1 h2 h3 h4 h5 h6
    obtain ⟨h7, h8⟩ := h; obtain ⟨h9, h10⟩ := h'
    dsimp only at h7 h8 h9 h10
    have : a = a' ∧ b = b' ∧ c = c' := by omega
    obtain ⟨rfl, rfl, rfl⟩ := this
    rfl
  · have h1 := hm (E (Sum.inr v'))
    simp at h1
  · have h1 := hm (E (Sum.inr v))
    simp at h1
  · have h1 := hm (E (Sum.inr v)); have h2 := hm (E (Sum.inl x)); have h3 := hm (E (Sum.inl y))
    have h4 := hm (E (Sum.inr v')); have h5 := hm (E (Sum.inl x'))
    have h6 := hm (E (Sum.inl y'))
    simp only [E_inl_eq_iff, E_inr_eq_iff, E_inl_eq_inr_iff, E_inr_eq_inl_iff, true_or, or_true,
      true_iff, iff_true, false_or, or_false] at h1 h2 h3 h4 h5 h6
    obtain ⟨h7, -⟩ := h; obtain ⟨h9, -⟩ := h'
    dsimp only at h7 h9
    have : x = x' ∧ y = y' := by omega
    obtain ⟨rfl, rfl⟩ := this
    subst h1
    rfl

omit [Fintype V] in
theorem exists_triMap_clique {i j k : Fin p} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ T, triMap G E T = {E (Sum.inl i), E (Sum.inl j), E (Sum.inl k)} := by
  rcases lt_or_gt_of_ne hij with h1 | h1 <;> rcases lt_or_gt_of_ne hik with h2 | h2 <;>
    rcases lt_or_gt_of_ne hjk with h3 | h3
  · exact ⟨Sum.inl ⟨(i, j, k), h1, h3⟩, rfl⟩
  · exact ⟨Sum.inl ⟨(i, k, j), h2, h3⟩, by
      ext; simp only [triMap, mem_insert, mem_singleton]; tauto⟩
  · exact absurd (h1.trans h3) (not_lt.mpr h2.le)
  · exact ⟨Sum.inl ⟨(k, i, j), h2, h1⟩, by
      ext; simp only [triMap, mem_insert, mem_singleton]; tauto⟩
  · exact ⟨Sum.inl ⟨(j, i, k), h1, h2⟩, by
      ext; simp only [triMap, mem_insert, mem_singleton]; tauto⟩
  · exact absurd (h3.trans h1) (not_lt.mpr h2.le)
  · exact ⟨Sum.inl ⟨(j, k, i), h3, h2⟩, by
      ext; simp only [triMap, mem_insert, mem_singleton]; tauto⟩
  · exact ⟨Sum.inl ⟨(k, j, i), h3, h1⟩, by
      ext; simp only [triMap, mem_insert, mem_singleton]; tauto⟩

omit [Fintype V] in
theorem exists_triMap_mixed {v : Fin m} {x y : Fin p} (hxy : x ≠ y)
    (hx : G.Adj (E (Sum.inr v)) (E (Sum.inl x))) (hy : G.Adj (E (Sum.inr v)) (E (Sum.inl y))) :
    ∃ T, triMap G E T = {E (Sum.inr v), E (Sum.inl x), E (Sum.inl y)} := by
  have hx' : x ∈ (Split.ofEquiv G E).N v := mem_filter.mpr ⟨mem_univ _, hx⟩
  have hy' : y ∈ (Split.ofEquiv G E).N v := mem_filter.mpr ⟨mem_univ _, hy⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨Sum.inr ⟨(v, x, y), h, hx', hy'⟩, rfl⟩
  · exact ⟨Sum.inr ⟨(v, y, x), h, hy', hx'⟩, by
      ext; simp only [triMap, mem_insert, mem_singleton]; tauto⟩

include hind in
theorem triMap_surj {t : Finset V} (ht : t ∈ G.cliqueFinset 3) : ∃ T, triMap G E T = t := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  obtain ⟨sa, rfl⟩ := E.surjective a
  obtain ⟨sb, rfl⟩ := E.surjective b
  obtain ⟨sc, rfl⟩ := E.surjective c
  have ne : ∀ {u w : Fin p}, G.Adj (E (Sum.inl u)) (E (Sum.inl w)) → u ≠ w :=
    fun h huw => h.ne (by rw [huw])
  rcases sa with i | u <;> rcases sb with j | v <;> rcases sc with k | w
  · exact exists_triMap_clique (ne hab) (ne hac) (ne hbc)
  · obtain ⟨T, hT⟩ := exists_triMap_mixed (ne hab) hac.symm hbc.symm
    exact ⟨T, hT.trans (by ext; simp only [mem_insert, mem_singleton]; tauto)⟩
  · obtain ⟨T, hT⟩ := exists_triMap_mixed (ne hac) hab.symm hbc
    exact ⟨T, hT.trans (by ext; simp only [mem_insert, mem_singleton]; tauto)⟩
  · exact absurd hbc (hind v w)
  · obtain ⟨T, hT⟩ := exists_triMap_mixed (ne hbc) hab hac
    exact ⟨T, hT⟩
  · exact absurd hac (hind u w)
  · exact absurd hab (hind u v)
  · exact absurd hab (hind u v)

include hcl in
theorem edgeMap_mem_edgesIn_iff (e : (Split.ofEquiv G E).Edge)
    (T : (Split.ofEquiv G E).Triangle) :
    edgeMap G E e ∈ edgesIn G (triMap G E T) ↔ (Split.ofEquiv G E).edgeMem e T := by
  rw [edgesIn, mem_filter]
  simp only [edgeMap_mem hcl e, true_and]
  rcases e with ⟨⟨i, j⟩, h⟩ | ⟨⟨v, x⟩, h⟩ <;> rcases T with ⟨⟨a, b, c⟩, h'⟩ | ⟨⟨w, y, z⟩, h'⟩ <;>
    simp only [edgeMap, triMap, Sym2.forall_mem_pair, mem_insert, mem_singleton, E_inl_eq_iff,
      E_inr_eq_iff, E_inl_eq_inr_iff, E_inr_eq_inl_iff, false_or, or_false, false_and,
      Split.edgeMem] <;>
    dsimp only at h h' <;> omega

omit [DecidableEq V] in
include hcl hind in
theorem edgeCount_eq : (Split.ofEquiv G E).edgeCount = G.edgeFinset.card := by
  classical
  have himg : G.edgeFinset = univ.image (edgeMap G E) := by
    ext e
    constructor
    · intro he
      obtain ⟨e₀, rfl⟩ := edgeMap_surj hind he
      exact mem_image_of_mem _ (mem_univ _)
    · intro he
      obtain ⟨e₀, -, rfl⟩ := mem_image.mp he
      exact edgeMap_mem hcl e₀
  rw [himg, card_image_of_injective _ edgeMap_injective, card_univ, Fintype.card_sum]
  have h1 : Fintype.card {e : Fin p × Fin p // e.1 < e.2} = p.choose 2 := by
    have := card_cliqueEdges_in (Split.ofEquiv G E) univ
    simp only [mem_univ, and_self, filter_true, card_univ, Fintype.card_fin] at this
    exact this
  have h2 : Fintype.card {e : Fin m × Fin p // e.2 ∈ (Split.ofEquiv G E).N e.1} =
      ∑ v, ((Split.ofEquiv G E).N v).card := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      fun v x => x ∈ (Split.ofEquiv G E).N v), Fintype.card_sigma]
    simp [Fintype.card_subtype]
  rw [Split.edgeCount, h1, h2]

omit [DecidableEq V] in
theorem n_eq : (Split.ofEquiv G E).n = Fintype.card V := by
  change p + Fintype.card (Fin m) = _
  rw [← Fintype.card_congr E, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

include hcl hind in
theorem nu3star_eq : (Split.ofEquiv G E).nu3star = fracPackingNumber G := by
  apply le_antisymm
  · refine csSup_le (Split.packingValues_nonempty _) ?_
    rintro _ ⟨w, hw, rfl⟩
    set w' : Finset V → ℝ :=
      fun t => ∑ T ∈ univ.filter (fun T => triMap G E T = t), w T with hw'
    have hval : ∑ t ∈ G.cliqueFinset 3, w' t = ∑ T, w T :=
      Finset.sum_fiberwise_of_maps_to (fun T _ => triMap_mem hcl T) w
    have hpack : IsFracTrianglePacking G w' := by
      refine ⟨fun t => sum_nonneg fun T _ => hw.1 T, fun e he => ?_⟩
      obtain ⟨e₀, rfl⟩ := edgeMap_surj hind he
      have hsum : ∑ t ∈ G.cliqueFinset 3 with edgeMap G E e₀ ∈ edgesIn G t, w' t
          = ∑ T ∈ univ.filter (fun T => edgeMap G E e₀ ∈ edgesIn G (triMap G E T)), w T := by
        have hfib : ∀ t, (if edgeMap G E e₀ ∈ edgesIn G t then w' t else 0) =
            ∑ T ∈ univ with triMap G E T = t,
              (if edgeMap G E e₀ ∈ edgesIn G (triMap G E T) then w T else 0) := by
          intro t
          split_ifs with hP
          · exact sum_congr rfl fun T hT => by rw [(mem_filter.mp hT).2, ite_eq_left hP]
          · exact (sum_eq_zero fun T hT => by rw [(mem_filter.mp hT).2, ite_eq_right hP]).symm
        rw [sum_filter, sum_congr rfl fun t _ => hfib t,
          Finset.sum_fiberwise_of_maps_to (fun T _ => triMap_mem hcl T), ← sum_filter]
      rw [hsum]
      refine le_trans (le_of_eq ?_) (hw.2 e₀)
      refine sum_congr ?_ fun _ _ => rfl
      ext T
      simp only [mem_filter, mem_univ, true_and, edgeMap_mem_edgesIn_iff hcl]
    rw [← hval]
    exact le_fracPackingNumber G hpack
  · refine csSup_le ⟨0, fun _ => 0, isFracTrianglePacking_zero G, by simp⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    have himg : G.cliqueFinset 3 = univ.image (triMap G E) := by
      ext t
      constructor
      · intro ht
        obtain ⟨T, rfl⟩ := triMap_surj hind ht
        exact mem_image_of_mem _ (mem_univ _)
      · intro ht
        obtain ⟨T, -, rfl⟩ := mem_image.mp ht
        exact triMap_mem hcl T
    have hval : ∑ T, w (triMap G E T) = ∑ t ∈ G.cliqueFinset 3, w t := by
      rw [himg, sum_image fun T _ T' _ h => triMap_injective h]
    rw [← hval]
    refine Split.nu3star_ge_of_feasible _ ⟨fun T => hw.1 _, fun e₀ => ?_⟩
    calc ∑ T ∈ univ.filter (fun T => (Split.ofEquiv G E).edgeMem e₀ T), w (triMap G E T)
        = ∑ t ∈ (univ.filter (fun T => (Split.ofEquiv G E).edgeMem e₀ T)).image (triMap G E),
            w t := (sum_image fun T _ T' _ h => triMap_injective h).symm
      _ ≤ ∑ t ∈ G.cliqueFinset 3 with edgeMap G E e₀ ∈ edgesIn G t, w t := by
          refine sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => hw.1 t
          obtain ⟨T, hT, rfl⟩ := mem_image.mp ht
          exact mem_filter.mpr ⟨triMap_mem hcl T,
            (edgeMap_mem_edgesIn_iff hcl e₀ T).mpr (mem_filter.mp hT).2⟩
      _ ≤ 1 := hw.2 _ (edgeMap_mem hcl e₀)

include hcl hind in
theorem Phi_eq : (Split.ofEquiv G E).Phi = (G.edgeFinset.card : ℝ) - 2 * fracPackingNumber G := by
  rw [Split.Phi, edgeCount_eq hcl hind, nu3star_eq hcl hind]

end Split.ofEquiv

end Model

/-- A split partition yields an identification `Fin p ⊕ Fin m ≃ V` that sends `Fin p` onto the
clique part and `Fin m` onto the independent part. -/
theorem SplitPartition.exists_equiv {V : Type*} [Finite V] {G : SimpleGraph V}
    (P : SplitPartition G) :
    ∃ (p m : ℕ) (E : Fin p ⊕ Fin m ≃ V), (∀ i, E (Sum.inl i) ∈ P.clique) ∧
      ∀ a, E (Sum.inr a) ∈ P.independent := by
  classical
  have := Fintype.ofFinite V
  refine ⟨Fintype.card P.clique, Fintype.card P.independent,
    (((Fintype.equivFin P.clique).symm.sumCongr (Fintype.equivFin P.independent).symm).trans
      (Equiv.Set.union P.disjoint).symm).trans ((Equiv.subtypeEquivProp P.cover).trans
      (Equiv.Set.univ V)), fun i => ((Fintype.equivFin P.clique).symm i).2,
    fun a => ((Fintype.equivFin P.independent).symm a).2⟩

/-- **Paper I, Theorem 1.1 (sharp form), on `SimpleGraph`.** -/
theorem split_main {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsSplit G) :
    (G.edgeFinset.card : ℝ) - 2 * fracPackingNumber G ≤
      (Fintype.card V : ℝ) ^ 2 / 6 + (Fintype.card V : ℝ) / 2 := by
  obtain ⟨P⟩ := hG
  obtain ⟨p, m, E, hEc, hEi⟩ := P.exists_equiv
  have hcl : ∀ i j : Fin p, i ≠ j → G.Adj (E (Sum.inl i)) (E (Sum.inl j)) := fun i j hij =>
    P.isClique (hEc i) (hEc j) (fun h => hij (by simpa using E.injective h))
  have hind : ∀ a b : Fin m, ¬ G.Adj (E (Sum.inr a)) (E (Sum.inr b)) := fun a b hab =>
    P.isIndepSet (hEi a) (hEi b) hab.ne hab
  have h := Split.paperI_main_sharp (Split.ofEquiv G E)
  rwa [Split.ofEquiv.Phi_eq hcl hind, Split.ofEquiv.n_eq] at h

/-- **Paper I, Theorem 1.1 (sharp form), cover version, on `SimpleGraph`.** -/
theorem split_main_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsSplit G) :
    (G.edgeFinset.card : ℝ) - 2 * fracCoverNumber G ≤
      (Fintype.card V : ℝ) ^ 2 / 6 + (Fintype.card V : ℝ) / 2 := by
  rw [fracCoverNumber_eq_fracPackingNumber]
  exact split_main G hG

end PaperI
