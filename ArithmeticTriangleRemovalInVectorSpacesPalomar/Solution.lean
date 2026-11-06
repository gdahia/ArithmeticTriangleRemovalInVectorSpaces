/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module -- shake: keep-all

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
import ArithmeticTriangleRemovalInVectorSpaces.ZMod

/-!
# A tight bound for Green's arithmetic triangle removal lemma in vector spaces

The statements of `Challenge.lean`, each proved by the library theorem with the same name without
the prime. The definitions `c` and `C` are those of the library.
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {p n : ℕ} [Fact p.Prime]

/-- **Theorem 1 of Fox and Lovász: the arithmetic triangle removal lemma.** If `X × Y × Z` has
fewer than `(ε / 3) ^ C p * N ^ 2` triangles `x + y + z = 0` in `Fin n → ZMod p`, where `N = p ^ n`,
then removing at most `ε * N` elements from `X`, `Y` and `Z` leaves no triangle. -/
theorem exists_subset_card_sdiff_add_le_forall_add_ne_zero' {ε : ℝ} (hε : 0 ≤ ε)
    {X Y Z : Finset (Fin n → ZMod p)}
    (h : #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < (ε / 3) ^ C p * (p ^ n) ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
      ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0 :=
  exists_subset_card_sdiff_add_le_forall_add_ne_zero hε h

/-- **The Kleinberg–Sawin–Speyer bound** (Theorem 2 of Fox and Lovász). If the triples
`(x i, y i, z i)` in `Fin n → ZMod p` satisfy `x i + y j + z k = 0` exactly when `i = j = k`, then
there are at most `p ^ ((1 - c p) * n)` of them. -/
theorem card_le_rpow_one_sub_c_mul' {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}
    (h : ∀ i j k, x i + y j + z k = 0 ↔ i = j ∧ j = k) :
    Fintype.card ι ≤ (p : ℝ) ^ ((1 - c p) * n) :=
  card_le_rpow_one_sub_c_mul h

/-- **Theorem 3 of Fox and Lovász.** If `X × Y × Z` contains `m` vertex-disjoint triangles
`(x i, y i, z i)` in `Fin n → ZMod p`, then it contains at least `(m / N) ^ C p * N ^ 2` triangles,
where `N = p ^ n`. -/
theorem div_pow_rpow_C_mul_sq_le_card_triangles' {ι : Type*} [Fintype ι]
    {x y z : ι → Fin n → ZMod p} {X Y Z : Finset (Fin n → ZMod p)} (hx : Injective x)
    (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y)
    (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι / (p : ℝ) ^ n) ^ C p * (p ^ n) ^ 2 ≤
      #((X ×ˢ Y ×ˢ Z).filter fun (u, v, w) ↦ u + v + w = 0) :=
  div_pow_rpow_C_mul_sq_le_card_triangles hx hy hz hxX hyY hzZ hsum

/-- **Asymptotic tightness of the arithmetic triangle removal lemma** (the "Furthermore" part of
Theorem 1 of Fox and Lovász). For every `η > 0` and every small `ε > 0`, any `δ` that works with
`ε` in the removal lemma in `Fin n → ZMod p` for every `n` satisfies `δ ≤ ε ^ (C p - η)`. -/
theorem exists_pos_forall_le_rpow_C_sub' {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ δ : ℝ,
      (∀ n (X Y Z : Finset (Fin n → ZMod p)),
        #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
          ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
            ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) →
      δ ≤ ε ^ (C p - η) :=
  exists_pos_forall_le_rpow_C_sub hη

end ArithmeticTriangleRemovalInVectorSpaces
