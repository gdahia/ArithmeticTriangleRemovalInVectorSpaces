/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exponent of the upper bound on `δ`

Section 3 of Fox and Lovász turns a multicolored sum-free family of `m` triples in
`Fin n → ZMod p` into the bound `δ * N ^ 2 ≤ m` for any `δ` that works in the removal lemma with
`ε < m / N`, where `N = p ^ n`. This file contains the real arithmetic that turns this bound into
`δ ≤ ε ^ (C p - η)`: the choice of `n` from `ε`, and the comparison of the exponents.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_lt_pow_le_inv_lt`: for `t > 1` and small `ε`
  there is a large `n` with `t ^ n ≤ ε⁻¹ < t ^ (n + 1)`.
* `ArithmeticTriangleRemovalInVectorSpaces.mul_pow_lt_of_rpow_mul_le`: the lower bound
  `(P ^ γ) ^ n ≤ ε⁻¹` makes `ε * P ^ n` smaller than a family of size `P ^ (a * n)`.
* `ArithmeticTriangleRemovalInVectorSpaces.inv_pow_le_mul_rpow`: the upper bound
  `ε⁻¹ < (P ^ κ⁻¹) ^ (n + 1)` gives `(P ^ n)⁻¹ ≤ P * ε ^ κ`.
* `ArithmeticTriangleRemovalInVectorSpaces.le_mul_rpow_one_add_of_mul_sq_le`: the bound
  `δ ≤ (P + P ^ 2) * ε ^ (1 + κ)` from `δ * N ^ 2 ≤ ε * N + 1` and `N⁻¹ ≤ P * ε ^ κ`.
* `ArithmeticTriangleRemovalInVectorSpaces.mul_rpow_le_rpow_sub`: a constant factor `A` is absorbed
  by lowering the exponent, for small `ε`.
-/

public section

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- For `t > 1` and `0 < ε < t ^ (-(n₀ + 1))` there is `n > n₀` with `t ^ n ≤ ε⁻¹ < t ^ (n + 1)`. -/
lemma exists_lt_pow_le_inv_lt {t ε : ℝ} (ht : 1 < t) {n₀ : ℕ} (hε₀ : 0 < ε)
    (hε : ε < (t ^ (n₀ + 1))⁻¹) : ∃ n, n₀ < n ∧ t ^ n ≤ ε⁻¹ ∧ ε⁻¹ < t ^ (n + 1) := by
  have hlt : t ^ (n₀ + 1) < ε⁻¹ := (lt_inv_comm₀ hε₀ (by positivity)).1 hε
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_pow₀ ht.le).trans hlt.le) ht
  exact ⟨n, Nat.succ_lt_succ_iff.1 ((pow_lt_pow_iff_right₀ ht).1 (hlt.trans hn')), hn, hn'⟩

/-- If `(P ^ γ) ^ n ≤ ε⁻¹` and `P ^ (a * n) ≤ m` with `1 - γ < a`, `P > 1` and `n > 0`, then
`ε * P ^ n < m`. -/
lemma mul_pow_lt_of_rpow_mul_le {P ε γ a m : ℝ} {n : ℕ} (hP : 1 < P) (hε : 0 < ε) (hn : 0 < n)
    (ha : 1 - γ < a) (h : (P ^ γ) ^ n ≤ ε⁻¹) (hm : P ^ (a * n) ≤ m) : ε * P ^ n < m := by
  calc ε * P ^ n ≤ ((P ^ γ) ^ n)⁻¹ * P ^ n := by
        grw [(le_inv_comm₀ hε (by positivity)).2 h]
    _ = P ^ ((1 - γ) * n) := by
        rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_neg (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
        ring_nf
    _ < P ^ (a * n) :=
        Real.rpow_lt_rpow_of_exponent_lt hP (mul_lt_mul_of_pos_right ha (by exact_mod_cast hn))
    _ ≤ m := hm

/-- If `ε⁻¹ < (P ^ κ⁻¹) ^ (n + 1)` with `P, ε, κ > 0`, then `(P ^ n)⁻¹ ≤ P * ε ^ κ`. -/
lemma inv_pow_le_mul_rpow {P ε κ : ℝ} {n : ℕ} (hP : 0 < P) (hε : 0 < ε) (hκ : 0 < κ)
    (h : ε⁻¹ < (P ^ κ⁻¹) ^ (n + 1)) : (P ^ n)⁻¹ ≤ P * ε ^ κ := by
  have := Real.rpow_lt_rpow (by positivity) h hκ
  rw [← Real.rpow_mul_natCast hP.le, ← Real.rpow_mul hP.le, mul_right_comm,
    inv_mul_cancel₀ hκ.ne', one_mul, Real.rpow_natCast, Real.inv_rpow hε.le,
    inv_lt_iff_one_lt_mul₀ (by positivity), pow_succ'] at this
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  linarith

/-- If `δ * N ^ 2 ≤ ε * N + 1` and `N⁻¹ ≤ P * ε ^ κ` with `κ ≥ 1` and `0 < ε ≤ 1`, then
`δ ≤ (P + P ^ 2) * ε ^ (1 + κ)`. -/
lemma le_mul_rpow_one_add_of_mul_sq_le {P N ε δ κ : ℝ} (hP : 0 < P) (hN : 0 < N) (hε₀ : 0 < ε)
    (hε₁ : ε ≤ 1) (hκ : 1 ≤ κ) (hNε : N⁻¹ ≤ P * ε ^ κ) (hδ : δ * N ^ 2 ≤ ε * N + 1) :
    δ ≤ (P + P ^ 2) * ε ^ (1 + κ) := by
  have hεκ : ε ^ κ ≤ ε := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε₀ hε₁ hκ
  calc δ ≤ (ε * N + 1) / N ^ 2 := (le_div_iff₀ (by positivity)).2 hδ
    _ = ε * N⁻¹ + N⁻¹ ^ 2 := by field_simp
    _ ≤ ε * (P * ε ^ κ) + (P * ε ^ κ) ^ 2 := by gcongr
    _ ≤ (P + P ^ 2) * (ε * ε ^ κ) := by
        nlinarith [Real.rpow_pos_of_pos hε₀ κ, mul_le_mul_of_nonneg_left hεκ
          (by positivity : 0 ≤ P ^ 2 * ε ^ κ)]
    _ = (P + P ^ 2) * ε ^ (1 + κ) := by rw [Real.rpow_add hε₀, Real.rpow_one]

/-- For `A > 0` and `0 < ε ≤ A⁻¹ ^ (2 / η)` with `ε ≤ 1`, lowering the exponent from `1 + κ` to
`C - η`, where `C - η / 2 ≤ 1 + κ`, absorbs the factor `A`: `A * ε ^ (1 + κ) ≤ ε ^ (C - η)`. -/
lemma mul_rpow_le_rpow_sub {A ε κ C η : ℝ} (hA : 0 < A) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 < η)
    (hκ : C - η / 2 ≤ 1 + κ) (hε : ε ≤ A⁻¹ ^ (2 / η)) : A * ε ^ (1 + κ) ≤ ε ^ (C - η) := by
  have hεη : ε ^ (η / 2) ≤ A⁻¹ := by
    grw [hε, ← Real.rpow_mul (by positivity), div_mul_div_cancel₀ (by positivity),
      div_self two_ne_zero, Real.rpow_one]
  calc A * ε ^ (1 + κ) ≤ A * ε ^ (C - η / 2) := by
        grw [Real.rpow_le_rpow_of_exponent_ge hε₀ hε₁ hκ]
    _ = A * ε ^ (η / 2) * ε ^ (C - η) := by
        rw [mul_assoc, ← Real.rpow_add hε₀]
        ring_nf
    _ ≤ ε ^ (C - η) := by
        grw [hεη, mul_inv_cancel₀ hA.ne', one_mul]

end ArithmeticTriangleRemovalInVectorSpaces
