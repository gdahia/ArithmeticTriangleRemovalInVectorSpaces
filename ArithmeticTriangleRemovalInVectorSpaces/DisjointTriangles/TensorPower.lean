/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.Embedding
import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.TensorPower

/-!
# Many triangles from disjoint triangles

This file proves Theorem 3 of Fox and Lovász: if `X × Y × Z` contains `m` vertex-disjoint
triangles in a finite vector space `V` over `ZMod p`, then it contains at least
`(m / #V) ^ C p * #V ^ 2` triangles. The pruning bound gives this up to a constant factor. The
`k`-th coordinatewise powers of `X`, `Y` and `Z` contain `m ^ k` vertex-disjoint triangles and
`D ^ k` triangles in a space of size `#V ^ k`, and letting `k` grow removes the constant factor.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_rpow_le_card_rpow_mul_card_triangles_rpow`: the
  bound `m ^ (1 + c p) ≤ #V ^ (1 - c p) * D ^ c p`.
* `ArithmeticTriangleRemovalInVectorSpaces.div_rpow_C_mul_sq_le_card_triangles`: Theorem 3 of Fox
  and Lovász.
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- If `m ^ (1 + c) ≤ N ^ (1 - c) * D ^ c`, then `(m / N) ^ (1 + 1 / c) * N ^ 2 ≤ D`. -/
lemma div_rpow_one_add_one_div_mul_sq_le {m N D c : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (hN : 0 < N)
    (hD : 0 ≤ D) (h : m ^ (1 + c) ≤ N ^ (1 - c) * D ^ c) :
    (m / N) ^ (1 + 1 / c) * N ^ 2 ≤ D := by
  have h' := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ 1 / c)
  rw [← Real.rpow_mul hm, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN.le,
    ← Real.rpow_mul hD, mul_one_div_cancel hc.ne', Real.rpow_one,
    (by field_simp; ring : (1 + c) * (1 / c) = 1 + 1 / c), ← div_le_iff₀' (by positivity)] at h'
  have hNC : N ^ (1 + 1 / c) = N ^ ((1 - c) * (1 / c)) * N ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN]
    congr 1
    field_simp
    ring
  rwa [Real.div_rpow hm hN.le, hNC, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity)]

variable {p : ℕ} [Fact p.Prime] {V ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [Fintype ι] {x y z : ι → V} {X Y Z : Finset V}

/-- If `X × Y × Z` contains `m` vertex-disjoint triangles `(x i, y i, z i)` and `D` triangles in
total, then `m ^ (1 + c p) ≤ #V ^ (1 - c p) * D ^ c p`. -/
lemma card_rpow_le_card_rpow_mul_card_triangles_rpow (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι : ℝ) ^ (1 + c p) ≤
      Fintype.card V ^ (1 - c p) * #(triangles X Y Z) ^ c p := by
  have hc := c_pos (Fact.out : p.Prime).two_le
  have hp : (0 : ℝ) < p := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, Real.zero_rpow (by linarith : 1 + c p ≠ 0)]
    positivity
  obtain ⟨i₀⟩ := id hι
  have hD : (0 : ℝ) < #(triangles X Y Z) :=
    Nat.cast_pos.2 (card_pos.2 ⟨_, mem_triangles.2 ⟨hxX i₀, hyY i₀, hzZ i₀, hsum i₀⟩⟩)
  refine le_of_forall_pow_le_mul_pow (M := 125 * p ^ 2 * ((p : ℝ) ^ 2) ^ (1 - c p) /
    (c p / (1 + c p) / 2) ^ (1 + c p))
    (mul_pos (Real.rpow_pos_of_pos (Nat.cast_pos.2 Fintype.card_pos) _)
      (Real.rpow_pos_of_pos hD _)) ?_
  intro k
  have := rpow_le_mul_card_rpow_mul_card_triangles_rpow (p := p)
    (X := Fintype.piFinset fun _ : Fin k ↦ X) (Y := Fintype.piFinset fun _ ↦ Y)
    (Z := Fintype.piFinset fun _ ↦ Z) (x := fun I t ↦ x (I t)) (y := fun I t ↦ y (I t))
    (z := fun I t ↦ z (I t)) (fun _ _ h ↦ funext fun t ↦ hx (congrFun h t))
    (fun _ _ h ↦ funext fun t ↦ hy (congrFun h t)) (fun _ _ h ↦ funext fun t ↦ hz (congrFun h t))
    (fun _ ↦ Fintype.mem_piFinset.2 fun _ ↦ hxX _) (fun _ ↦ Fintype.mem_piFinset.2 fun _ ↦ hyY _)
    (fun _ ↦ Fintype.mem_piFinset.2 fun _ ↦ hzZ _) (fun _ ↦ funext fun _ ↦ hsum _)
  rw [card_triangles_piFinset, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin] at this
  push_cast at this
  rw [mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_pow_comm (Nat.cast_nonneg (Fintype.card ι)),
    ← Real.rpow_pow_comm (Nat.cast_nonneg (Fintype.card V)),
    ← Real.rpow_pow_comm (Nat.cast_nonneg #(triangles X Y Z))] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_pow]
  linarith

/-- **Theorem 3 of Fox and Lovász.** If `X × Y × Z` contains `m` vertex-disjoint triangles
`(x i, y i, z i)` in a finite vector space `V` over `ZMod p`, then it contains at least
`(m / #V) ^ C p * #V ^ 2` triangles. -/
theorem div_rpow_C_mul_sq_le_card_triangles (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    ((Fintype.card ι : ℝ) / Fintype.card V) ^ C p * Fintype.card V ^ 2 ≤ #(triangles X Y Z) :=
  div_rpow_one_add_one_div_mul_sq_le (c_pos (Fact.out : p.Prime).two_le) (Nat.cast_nonneg _)
    (Nat.cast_pos.2 Fintype.card_pos) (Nat.cast_nonneg _)
    (card_rpow_le_card_rpow_mul_card_triangles_rpow hx hy hz hxX hyY hzZ hsum)

end ArithmeticTriangleRemovalInVectorSpaces
