/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A tight bound for Green's arithmetic triangle removal lemma in vector spaces

The main results of Fox and Lovász, *A tight bound for Green's arithmetic triangle removal lemma
in vector spaces*, [arXiv:1606.01230](https://arxiv.org/abs/1606.01230), in `Fin n → ZMod p`:
Theorems 1, 2 and 3, including the bound `δ ≤ ε ^ (C p - o(1))` of Theorem 1, and the values of
`c 2` and `c 3`. A triangle of `X × Y × Z` is a triple
`(x, y, z)` with `x + y + z = 0`.

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The exponent `c p` of Kleinberg, Sawin and Speyer, defined by
`p ^ (1 - c p) = ⨅ x ∈ (0, 1), x ^ (-(p - 1) / 3) * (1 + x + ⋯ + x ^ (p - 1))`. The numeral `3` is
a natural number, so that the definition contains no proofs. -/
noncomputable def c (p : ℕ) : ℝ :=
  1 - Real.logb p
    (⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / (3 : ℕ)) * ∑ j ∈ range p, (x : ℝ) ^ j)

/-- The exponent `C p = 1 + 1 / c p` of the arithmetic triangle removal lemma in
`Fin n → ZMod p`. -/
noncomputable def C (p : ℕ) : ℝ :=
  1 + 1 / c p

variable {p n : ℕ} [Fact p.Prime]

/-- **Theorem 1 of Fox and Lovász: the arithmetic triangle removal lemma.** If `X × Y × Z` has
fewer than `(ε / 3) ^ C p * N ^ 2` triangles `x + y + z = 0` in `Fin n → ZMod p`, where `N = p ^ n`,
then removing at most `ε * N` elements from `X`, `Y` and `Z` leaves no triangle. -/
theorem exists_subset_card_sdiff_add_le_forall_add_ne_zero' {ε : ℝ} (hε : 0 ≤ ε)
    {X Y Z : Finset (Fin n → ZMod p)}
    (h : #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < (ε / 3) ^ C p * (p ^ n) ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
      ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0 := by
  sorry

/-- **The Kleinberg–Sawin–Speyer bound** (Theorem 2 of Fox and Lovász). If the triples
`(x i, y i, z i)` in `Fin n → ZMod p` satisfy `x i + y j + z k = 0` exactly when `i = j = k`, then
there are at most `p ^ ((1 - c p) * n)` of them. -/
theorem card_le_rpow_one_sub_c_mul' {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}
    (h : ∀ i j k, x i + y j + z k = 0 ↔ i = j ∧ j = k) :
    Fintype.card ι ≤ (p : ℝ) ^ ((1 - c p) * n) := by
  sorry

/-- **Theorem 3 of Fox and Lovász.** If `X × Y × Z` contains `m` vertex-disjoint triangles
`(x i, y i, z i)` in `Fin n → ZMod p`, then it contains at least `(m / N) ^ C p * N ^ 2` triangles,
where `N = p ^ n`. -/
theorem div_pow_rpow_C_mul_sq_le_card_triangles' {ι : Type*} [Fintype ι]
    {x y z : ι → Fin n → ZMod p} {X Y Z : Finset (Fin n → ZMod p)} (hx : Injective x)
    (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y)
    (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι / (p : ℝ) ^ n) ^ C p * (p ^ n) ^ 2 ≤
      #((X ×ˢ Y ×ˢ Z).filter fun (u, v, w) ↦ u + v + w = 0) := by
  sorry

/-- **Asymptotic tightness of the arithmetic triangle removal lemma** (the "Furthermore" part of
Theorem 1 of Fox and Lovász). For every `η > 0` and every small `ε > 0`, any `δ` that works with
`ε` in the removal lemma in `Fin n → ZMod p` for every `n` satisfies `δ ≤ ε ^ (C p - η)`. -/
theorem exists_pos_forall_le_rpow_C_sub' {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ δ : ℝ,
      (∀ n (X Y Z : Finset (Fin n → ZMod p)),
        #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
          ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
            ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) →
      δ ≤ ε ^ (C p - η) := by
  sorry

/-- **The exponent `c 2`.** `c 2 = 5 / 3 - logb 2 3`. -/
theorem c_two' : c 2 = 5 / 3 - Real.logb 2 3 := by
  sorry

/-- **The exponent `c 3`.** With `a = (√33 - 1) / 8` and
`b = a ^ (-2 / 3) + a ^ (1 / 3) + a ^ (4 / 3)`, `c 3 = 1 - log b / log 3`. -/
theorem c_three' {a : ℝ} (ha : a = (√33 - 1) / 8) :
    c 3 = 1 - Real.log (a ^ (-2 / 3 : ℝ) + a ^ (1 / 3 : ℝ) + a ^ (4 / 3 : ℝ)) / Real.log 3 := by
  sorry

end ArithmeticTriangleRemovalInVectorSpaces
