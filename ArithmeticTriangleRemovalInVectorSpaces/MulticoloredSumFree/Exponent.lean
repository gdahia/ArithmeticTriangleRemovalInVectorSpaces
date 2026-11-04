/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The exponents `c_p` and `C_p`

The exponent `c_p` of Kleinberg, Sawin and Speyer is defined by
`p ^ (1 - c_p) = ⨅ x ∈ (0, 1), x ^ (-(p - 1) / 3) * (1 + x + ⋯ + x ^ (p - 1))`. A multicolored
sum-free family in `Fin n → ZMod p` has at most `p ^ ((1 - c_p) * n)` members, and the exponent of
the arithmetic triangle removal lemma in `Fin n → ZMod p` is `C_p = 1 + 1 / c_p`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.c p`: the exponent `c_p`.
* `ArithmeticTriangleRemovalInVectorSpaces.C p`: the exponent `C_p = 1 + 1 / c_p`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.rpow_one_sub_c_le`: `p ^ (1 - c p)` is at most the
  value of `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` at each `x ∈ (0, 1)`.
* `ArithmeticTriangleRemovalInVectorSpaces.le_rpow_one_sub_c`: it is the largest such number.
* `ArithmeticTriangleRemovalInVectorSpaces.c_pos` and
  `ArithmeticTriangleRemovalInVectorSpaces.c_lt_one`: `0 < c p < 1` for `p ≥ 2`.
-/

@[expose] public section

open Finset Filter Topology

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The exponent `c_p` of Kleinberg, Sawin and Speyer, defined by
`p ^ (1 - c_p) = ⨅ x ∈ (0, 1), x ^ (-(p - 1) / 3) * (1 + x + ⋯ + x ^ (p - 1))`. The numeral is a
natural number, so that the definition contains no proofs. -/
noncomputable def c (p : ℕ) : ℝ :=
  1 - Real.logb p
    (⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / (3 : ℕ)) * ∑ j ∈ range p, (x : ℝ) ^ j)

/-- The exponent `C_p = 1 + 1 / c_p` of the arithmetic triangle removal lemma in
`Fin n → ZMod p`. -/
noncomputable def C (p : ℕ) : ℝ :=
  1 + 1 / c p

variable {p : ℕ}

/-- For `0 < x < 1` and `p ≥ 2`, `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j ≥ 3 / 2`. -/
lemma three_div_two_le_rpow_mul_sum (hp : 2 ≤ p) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    3 / 2 ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j := by
  have hroot : x ^ (1 / 3 : ℝ) ≤ 1 + 1 / 3 * (x - 1) := by
    simpa using rpow_one_add_le_one_add_mul_self (by linarith : -1 ≤ x - 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hneg : 3 / (2 + x) ≤ x ^ (-((p : ℝ) - 1) / 3) := by
    grw [← Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁.le
      (by linarith : -((p : ℝ) - 1) / 3 ≤ -(1 / 3))]
    rw [Real.rpow_neg hx₀.le, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    linarith
  have hsum : 1 + x ≤ ∑ j ∈ range p, x ^ j := by
    grw [← sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hp) fun j _ _ ↦ by positivity]
    simp [add_comm]
  grw [← hneg, ← hsum]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- The value of the infimum defining `c p`. -/
lemma rpow_one_sub_c (hp : 2 ≤ p) :
    (p : ℝ) ^ (1 - c p) =
      ⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, (x : ℝ) ^ j := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  rw [c, sub_sub_cancel, Nat.cast_ofNat, Real.rpow_logb (by positivity)
    (by exact_mod_cast (by grind : p ≠ 1))]
  exact (by norm_num : (0 : ℝ) < 3 / 2).trans_le
    (le_ciInf fun ⟨x, hx₀, hx₁⟩ ↦ three_div_two_le_rpow_mul_sum hp hx₀ hx₁)

/-- `p ^ (1 - c p)` is at most `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` for `0 < x < 1`. -/
lemma rpow_one_sub_c_le (hp : 2 ≤ p) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    (p : ℝ) ^ (1 - c p) ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j := by
  rw [rpow_one_sub_c hp]
  refine ciInf_le ⟨0, ?_⟩ (⟨x, hx₀, hx₁⟩ : Set.Ioo (0 : ℝ) 1)
  rintro _ ⟨⟨y, hy₀, -⟩, rfl⟩
  positivity

/-- `p ^ (1 - c p)` is the largest lower bound of `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` on
`(0, 1)`. -/
lemma le_rpow_one_sub_c (hp : 2 ≤ p) {b : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 → b ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) :
    b ≤ (p : ℝ) ^ (1 - c p) := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  rw [rpow_one_sub_c hp]
  exact le_ciInf fun ⟨x, hx₀, hx₁⟩ ↦ h x hx₀ hx₁

/-- The function `x ↦ x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` takes a value smaller than `p` on
`(0, 1)`: its derivative at `1` is `p * (p - 1) / 6 > 0`. -/
lemma exists_rpow_mul_sum_lt (hp : 2 ≤ p) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j < p := by
  set f : ℝ → ℝ := fun x ↦ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j
  have hderiv : HasDerivAt f (-((p : ℝ) - 1) / 3 * p + ∑ j ∈ range p, (j : ℝ)) 1 := by
    have := (Real.hasDerivAt_rpow_const (p := -((p : ℝ) - 1) / 3) (Or.inl one_ne_zero)).fun_mul
      (HasDerivAt.fun_sum fun j (_ : j ∈ range p) ↦ hasDerivAt_pow j (1 : ℝ))
    simpa [f] using this
  have hpos : 0 < -((p : ℝ) - 1) / 3 * p + ∑ j ∈ range p, (j : ℝ) := by
    have h := sum_range_id_mul_two p
    rw [← Nat.cast_inj (R := ℝ)] at h
    push_cast [Nat.cast_sub (by grind : 1 ≤ p)] at h
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left
    (nhdsWithin_mono _ fun y (hy : y ∈ Set.Iio 1) ↦ hy.ne)
  obtain ⟨x, hslope, hx₀, hx₁⟩ :=
    ((hslope.eventually (lt_mem_nhds hpos)).and (Ioo_mem_nhdsLT one_pos)).exists
  refine ⟨x, hx₀, hx₁, ?_⟩
  rw [slope_def_field, lt_div_iff_of_neg (by linarith), zero_mul, sub_neg] at hslope
  simpa [f] using hslope

/-- **`c_p` is positive.** -/
lemma c_pos (hp : 2 ≤ p) : 0 < c p := by
  obtain ⟨x, hx₀, hx₁, hx⟩ := exists_rpow_mul_sum_lt hp
  have hlt := (rpow_one_sub_c_le hp hx₀ hx₁).trans_lt hx
  have h := Real.rpow_lt_rpow_left_iff (x := (p : ℝ)) (y := 1 - c p) (z := 1)
    (by exact_mod_cast (by grind : 1 < p))
  rw [Real.rpow_one] at h
  linarith [h.1 hlt]

/-- **`c_p` is less than one.** -/
lemma c_lt_one (hp : 2 ≤ p) : c p < 1 := by
  have h := le_rpow_one_sub_c hp fun x hx₀ hx₁ ↦ three_div_two_le_rpow_mul_sum hp hx₀ hx₁
  by_contra! hc
  have := Real.rpow_le_rpow_of_exponent_le (x := (p : ℝ)) (by exact_mod_cast (by grind : 1 ≤ p))
    (by linarith : 1 - c p ≤ 0)
  rw [Real.rpow_zero] at this
  linarith

end ArithmeticTriangleRemovalInVectorSpaces
