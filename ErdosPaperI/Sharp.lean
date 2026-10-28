/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ErdosPaperI.Statement

/-!
  Paper I v1.1 candidate — the sharpened bound  Φ ≤ n²/6 + n/2.

  `paperI_main` (the frozen v1.0 artifact) proves the weaker `Φ ≤ n²/6 + n`. The proof
  actually yields `n²/6 + n/2`: (8.3) already gives `Φ ≤ (p+q)²/6 + p/2 + b₁`, and the
  final step of §8 discards quadratic slack in `b₁ + |I₀|` that pays for the linear term.

  This file adds the sharpened statement WITHOUT touching the frozen `PaperI` development;
  it re-uses the public lemmas `nu3star_ge_Vcom`, `Mcov_lower`, `edgeCount_eq`.
-/

@[expose] public section

namespace PaperI

open scoped BigOperators

/-- The sharp assembly arithmetic. The side hypothesis `1 ≤ b₁ → 1 ≤ p` is forced by the
model (a degree-one independent vertex has its neighbour in `K`). Over `ℝ` with only
`b₁ ≥ 0` the inequality is false, so `b₁` must be a natural. -/
lemma assembly_sharp (p q b i : ℕ) (hside : 1 ≤ b → 1 ≤ p) :
    ((p : ℝ) + q) ^ 2 / 6 + (p : ℝ) / 2 + (b : ℝ)
      ≤ ((p : ℝ) + q + b + i) ^ 2 / 6 + ((p : ℝ) + q + b + i) / 2 := by
  have hp : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hq : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hbn : (0:ℝ) ≤ (b:ℝ) := by positivity
  have hi : (0:ℝ) ≤ (i:ℝ) := by positivity
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    nlinarith [sq_nonneg (i:ℝ), mul_nonneg (add_nonneg hp hq) hi, hq, hi]
  · have hpR : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hside hb1
    have hbR : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb1
    have hkey : (0:ℝ) ≤ (b:ℝ) + 2*(p:ℝ) + 2*(q:ℝ) - 3 := by nlinarith
    nlinarith [mul_nonneg hbn hkey, sq_nonneg (i:ℝ),
      mul_nonneg (add_nonneg hp hq) hi, mul_nonneg hbn hi, hq, hi]

namespace Split
variable (G : Split)

/-- `q + b₁ ≤ |I|`: the degree-≥2 and degree-1 independent vertices are disjoint subsets. -/
theorem q_add_b1_le_card : G.q + G.b1 ≤ Fintype.card G.ι := by
  classical
  have hdisj : Disjoint (Finset.univ.filter (fun v : G.ι => 2 ≤ (G.N v).card))
      (Finset.univ.filter (fun v : G.ι => (G.N v).card = 1)) := by
    simp only [Finset.disjoint_left, Finset.mem_filter]
    rintro v ⟨_, h2⟩ ⟨_, h1⟩; omega
  have h := Finset.card_union_of_disjoint hdisj
  have hqb : G.q + G.b1 =
      ((Finset.univ.filter (fun v : G.ι => 2 ≤ (G.N v).card)) ∪
        (Finset.univ.filter (fun v : G.ι => (G.N v).card = 1))).card := by
    rw [h]; rfl
  rw [hqb, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- A degree-one independent vertex forces the clique to be nonempty: `1 ≤ b₁ → 1 ≤ p`. -/
theorem one_le_p_of_one_le_b1 : 1 ≤ G.b1 → 1 ≤ G.p := by
  intro hb
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by simpa [Split.b1] using hb)
  rw [Finset.mem_filter] at hv
  have hne : (G.N v).Nonempty := Finset.card_pos.mp (by rw [hv.2]; norm_num)
  obtain ⟨x, _⟩ := hne
  have := x.isLt; omega

/-- **Paper I v1.1, sharpened.** `Φ ≤ n²/6 + n/2`. -/
theorem paperI_main_sharp : G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 := by
  have h1 := G.nu3star_ge_Vcom
  have h2 := G.Mcov_lower
  have h3 := G.edgeCount_eq
  have hRq : ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ)
      = (2 * (G.p : ℝ) ^ 2 - 2 * (G.p : ℝ) * (G.q : ℝ) - (G.q : ℝ) ^ 2) / 12 := by
    simp only [Rq]; push_cast; ring
  have hchoose : (Nat.choose G.p 2 : ℝ) = (G.p : ℝ) * ((G.p : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hPhi : G.Phi ≤ (Nat.choose G.p 2 : ℝ) + (G.b1 : ℝ)
      - 2 * (((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2) := by
    have hd : G.Phi = (G.edgeCount : ℝ) - 2 * G.nu3star := rfl
    linarith [h1, h2, h3, hd]
  rw [hchoose, hRq] at hPhi
  -- (8.3): hPhi now says  Φ ≤ (p+q)²/6 + p/2 + b₁  (up to `ring`)
  have hqb1 := G.q_add_b1_le_card
  have hkey := assembly_sharp G.p G.q G.b1 (Fintype.card G.ι - G.q - G.b1)
    G.one_le_p_of_one_le_b1
  have hsum : G.p + G.q + G.b1 + (Fintype.card G.ι - G.q - G.b1) = G.n := by
    rw [G.n_eq]; omega
  have hcast : (G.p : ℝ) + (G.q : ℝ) + (G.b1 : ℝ)
      + ((Fintype.card G.ι - G.q - G.b1 : ℕ) : ℝ) = (G.n : ℝ) := by exact_mod_cast hsum
  rw [hcast] at hkey
  nlinarith [hPhi, hkey]

end Split
end PaperI
