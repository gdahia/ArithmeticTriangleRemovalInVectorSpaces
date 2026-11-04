/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import Mathlib.LinearAlgebra.Dimension.Finrank
import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.SliceRank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# The Kleinberg–Sawin–Speyer bound

A multicolored sum-free family in a finite vector space `G` over `ZMod p` has at most
`#G ^ (1 - c p)` members. The slice rank bound and the Chernoff bound give this up to a factor `3`,
and the bound for the coordinatewise powers of the family removes the factor, as in Kleinberg,
Sawin and Speyer.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_three_mul_pow`: the bound
  `3 * (x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j) ^ finrank (ZMod p) G` for `0 < x ≤ 1`.
* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_card_rpow`: the bound
  `#G ^ (1 - c p)`.
-/

public section

open Finset Module

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- If `a ^ k ≤ M * b ^ k` for every `k` and `b > 0`, then `a ≤ b`. -/
lemma le_of_forall_pow_le_mul_pow {a b M : ℝ} (hb : 0 < b) (h : ∀ k : ℕ, a ^ k ≤ M * b ^ k) :
    a ≤ b := by
  by_contra! hba
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M ((one_lt_div hb).2 hba)
  have := h k
  rw [div_pow, lt_div_iff₀ (by positivity)] at hk
  linarith

variable {p : ℕ} [Fact p.Prime] {G ι : Type*} [AddCommGroup G] [Module (ZMod p) G] [Fintype ι]
  {x y z : ι → G}

/-- A multicolored sum-free family in a finite vector space `G` over `ZMod p` has at most
`3 * (t ^ (-(p - 1) / 3) * ∑ j ∈ range p, t ^ j) ^ finrank (ZMod p) G` members, for `0 < t ≤ 1`. -/
lemma IsMulticoloredSumFree.card_le_three_mul_pow [Finite G] (h : IsMulticoloredSumFree x y z)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    Fintype.card ι ≤
      3 * (t ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, t ^ j) ^ finrank (ZMod p) G := by
  let e := (Module.finBasis (ZMod p) G).equivFun
  have := (h.map e.toLinearMap.toAddMonoidHom e.injective).card_le_three_mul_card
  grw [← card_lowDegreeExponents_le (Fact.out : p.Prime).one_lt.le _ ht₀ ht₁]
  exact_mod_cast this

/-- **The Kleinberg–Sawin–Speyer bound.** A multicolored sum-free family in a finite vector space
`G` over `ZMod p` has at most `#G ^ (1 - c p)` members. -/
theorem IsMulticoloredSumFree.card_le_card_rpow [Fintype G] (h : IsMulticoloredSumFree x y z) :
    (Fintype.card ι : ℝ) ≤ Fintype.card G ^ (1 - c p) := by
  have hp := (Fact.out : p.Prime).two_le
  have hpow (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) : Fintype.card ι ≤
      (t ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, t ^ j) ^ finrank (ZMod p) G := by
    refine le_of_forall_pow_le_mul_pow (M := 3)
      (pow_pos (by linarith [three_div_two_le_rpow_mul_sum hp ht₀ ht₁]) _) ?_
    intro k
    have := (h.pi (Fin k)).card_le_three_mul_pow (p := p) ht₀ ht₁.le
    rw [finrank_pi_fintype, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, pow_mul',
      Fintype.card_fun, Fintype.card_fin] at this
    exact_mod_cast this
  rw [card_eq_pow_finrank (K := ZMod p) (V := G), ZMod.card, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
  generalize finrank (ZMod p) G = d at hpow ⊢
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using hpow (1 / 2) (by norm_num) (by norm_num)
  rw [← Real.rpow_inv_natCast_pow (Nat.cast_nonneg (Fintype.card ι)) hd.ne']
  gcongr
  refine le_rpow_one_sub_c hp ?_
  intro t ht₀ ht₁
  rw [Real.rpow_inv_le_iff_of_pos (by positivity)
    (by linarith [three_div_two_le_rpow_mul_sum hp ht₀ ht₁]) (by positivity), Real.rpow_natCast]
  exact hpow t ht₀ ht₁

end ArithmeticTriangleRemovalInVectorSpaces
