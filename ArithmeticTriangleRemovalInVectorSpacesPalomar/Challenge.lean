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
Theorems 1, 2 and 3, including the bound `δ ≤ ε ^ (C p - η)` of Theorem 1 for
`0 < ε < tightnessEps p η`, an explicit function of `p` and `η`. A triangle of `X × Y × Z` is a
triple `(x, y, z)` with `x + y + z = 0`.

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The exponent `c p` of Kleinberg, Sawin and Speyer, defined by
`p ^ (1 - c p) = ⨅ x ∈ (0, 1), x ^ (-(p - 1) / 3) * (1 + x + ⋯ + x ^ (p - 1))`. -/
noncomputable def c (p : ℕ) : ℝ :=
  1 - Real.logb p
    (⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, (x : ℝ) ^ j)

/-- The exponent `C p = 1 + 1 / c p` of the arithmetic triangle removal lemma in
`Fin n → ZMod p`. -/
noncomputable def C (p : ℕ) : ℝ :=
  1 + 1 / c p

/-- The dimension `n₀ = ⌈(2 ^ (p + 3) * p ^ 10 / η) ^ 2⌉ + p ^ 4 + 1` from which on
`Fin n → ZMod p` contains a multicolored sum-free family with at least `p ^ ((1 - c p - η) * n)`
members. -/
noncomputable def sumFreeDim (p : ℕ) (η : ℝ) : ℕ :=
  ⌈(2 ^ (p + 3) * p ^ 10 / η) ^ 2⌉₊ + p ^ 4 + 1

/-- The bound `ε₀ = p ^ (-(n₀ + 1))`, where `n₀ = sumFreeDim p η'` with
`η' = c p * min (1 - c p) (c p * η / 2) / 2`. For `0 < ε < ε₀`, every `δ` that works with `ε` in
the arithmetic triangle removal lemma in `Fin n → ZMod p` for every `n` satisfies
`δ ≤ ε ^ (C p - η)`. -/
noncomputable def tightnessEps (p : ℕ) (η : ℝ) : ℝ :=
  ((p : ℝ) ^ (sumFreeDim p (c p * min (1 - c p) (c p * η / 2) / 2) + 1))⁻¹

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
Theorem 1 of Fox and Lovász). For every `η > 0` and every `0 < ε < tightnessEps p η`, any `δ` that
works with `ε` in the removal lemma in `Fin n → ZMod p` for every `n` satisfies
`δ ≤ ε ^ (C p - η)`. -/
theorem le_rpow_C_sub_of_forall_exists_subset' {η ε δ : ℝ} (hη : 0 < η) (hε₀ : 0 < ε)
    (hε : ε < tightnessEps p η)
    (hδ : ∀ n (X Y Z : Finset (Fin n → ZMod p)),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ ≤ ε ^ (C p - η) := by
  sorry

end ArithmeticTriangleRemovalInVectorSpaces
