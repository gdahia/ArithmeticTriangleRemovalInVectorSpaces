/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# The size of a type class

The vectors in `ℕ ^ n` obtained by permuting the entries of a vector `a` form its type class. If
the value `k` appears `D k` times in `a`, the type class has `n! / ∏ k, D k !` elements. This file
bounds the logarithm of this number from below by `∑ k, D k * log (1 / ψ k)` up to an error
controlled by the distance between `D` and `n ψ`, for every probability vector `ψ`. This is
Lemma 3.1 of Kleinberg, Sawin and Speyer, with the comparison between entropy and cross entropy.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.typeClass a`: the vectors obtained by permuting the
  entries of `a`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_typeClass_mul_prod_factorial`: the type class of
  `a` has `n! / ∏ k, D k !` elements.
* `ArithmeticTriangleRemovalInVectorSpaces.le_log_card_typeClass`: the lower bound on its
  logarithm.
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n N : ℕ}

/-- The type class of `a`: the vectors obtained by permuting the entries of `a`. -/
@[expose] def typeClass (a : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  univ.image fun σ : Equiv.Perm (Fin n) ↦ a ∘ σ

lemma mem_typeClass {a b : Fin n → ℕ} : b ∈ typeClass a ↔ ∃ σ : Equiv.Perm (Fin n), a ∘ σ = b := by
  simp [typeClass]

/-- **Orbit-stabilizer for type classes.** The type class of `a` times `∏ k, D k !` is `n!`. -/
lemma card_typeClass_mul_prod_factorial (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) :
    #(typeClass a) * ∏ k ∈ range (N + 1), (#{r | a r = k}).factorial = n.factorial := by
  unfold typeClass
  have hstab := DomMulAct.stabilizer_card' a
  have hprod : ∏ k ∈ range (N + 1), (#{r | a r = k}).factorial =
      ∏ i ∈ univ.image a, (Fintype.card {r // a r = i}).factorial := by
    rw [← prod_subset (s₁ := univ.image a) (s₂ := range (N + 1))]
    · congr with k
      rw [Fintype.card_subtype]
    · intro k hk
      simp only [mem_image, mem_univ, true_and] at hk
      obtain ⟨r, rfl⟩ := hk
      simp only [mem_range]
      grind [ha r]
    · intro k _ hk
      simp only [mem_image, mem_univ, true_and, not_exists] at hk
      simp [filter_eq_empty_iff.2 fun r _ ↦ hk r]
  have hperm : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [hprod, ← hstab, ← hperm, ← card_univ (α := Equiv.Perm (Fin n)),
    card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin n) ↦ a ∘ σ)
      (t := univ.image fun σ : Equiv.Perm (Fin n) ↦ a ∘ σ) (by simp)]
  rw [sum_const_nat]
  intro w hw
  obtain ⟨τ, -, rfl⟩ := mem_image.1 hw
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ⟨fun σ ↦ ⟨σ.1 * τ⁻¹, ?_⟩, fun g ↦ ⟨g.1 * τ, ?_⟩, ?_, ?_⟩
  · ext r
    have := congr_fun σ.2 (τ⁻¹ r)
    simpa using this
  · ext r
    have := congr_fun g.2 (τ r)
    simpa using this
  · intro σ
    simp
  · intro g
    simp

/-- `n log n - n ≤ log n!`. -/
lemma mul_log_sub_le_log_factorial (n : ℕ) : n * log n - n ≤ log n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n)] at h
  have := log_le_log (pow_pos (by exact_mod_cast hn) n) h
  rw [log_mul (by positivity) (by positivity), log_exp, log_pow] at this
  linarith

/-- `log D! ≤ D log D - D + 1 + log (D + 1)`, from the monotonicity of the Stirling sequence. -/
lemma log_factorial_le (D : ℕ) : log D.factorial ≤ D * log D - D + 1 + log (D + 1) := by
  rcases D with _ | m
  · simp
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  simp only [Function.comp_apply, Stirling.log_stirlingSeq_formula, Nat.succ_eq_add_one,
    zero_add, Nat.factorial_one, Nat.cast_one, log_one, mul_one, one_div, log_inv, log_exp] at h
  push_cast at h ⊢
  rw [log_mul (by norm_num) (by positivity), div_eq_mul_inv, log_mul (by positivity)
    (by positivity), log_inv, log_exp] at h
  have h₁ := log_nonneg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)] : (1 : ℝ) ≤ m + 1)
  have h₂ := log_le_log (by positivity) (by linarith : (m + 1 : ℝ) ≤ m + 1 + 1)
  linarith

/-- The logarithm of a multinomial coefficient is at least the entropy term
`∑ k, D k * log (n / D k)` minus `|s| (1 + log (n + 1))`. -/
lemma sum_mul_log_div_sub_le_log {s : Finset ℕ} (D : ℕ → ℕ) (hD : ∑ k ∈ s, D k = n) :
    ∑ k ∈ s, D k * log (n / D k) - #s * (1 + log (n + 1)) ≤
      log n.factorial - ∑ k ∈ s, log (D k).factorial := by
  have hDn (k : ℕ) (hk : k ∈ s) : (D k : ℝ) ≤ n := by
    rw [← hD]
    exact_mod_cast single_le_sum (fun _ _ ↦ Nat.zero_le _) hk
  have hterm (k : ℕ) (hk : k ∈ s) :
      D k * log (n / D k) - (1 + log (n + 1)) ≤ D k * log n - (D k * log (D k) - D k + 1 +
        log (D k + 1)) - D k := by
    have := log_le_log (by positivity) (by linarith [hDn k hk] : (D k + 1 : ℝ) ≤ n + 1)
    rcases Nat.eq_zero_or_pos (D k) with h0 | hpos
    · simp [h0]
      linarith [log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)] : (1 : ℝ) ≤ n + 1)]
    · have hpos' : (0 : ℝ) < D k := by exact_mod_cast hpos
      rw [log_div (by linarith [hDn k hk]) hpos'.ne']
      linarith
  have hsum : (n : ℝ) = ∑ k ∈ s, (D k : ℝ) := by exact_mod_cast hD.symm
  have := sum_le_sum hterm
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at this
  simp only [sum_sub_distrib, ← sum_mul] at this
  grw [← mul_log_sub_le_log_factorial, sum_le_sum fun k _ ↦ log_factorial_le (D k)]
  rw [hsum] at this ⊢
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one] at this ⊢
  linarith

/-- **Entropy and cross entropy.** For a probability vector `ψ > 0` and counts `D` summing to `n`,
`∑ k, D k * log (n / D k) ≥ ∑ k, D k * log (1 / ψ k) - ∑ k, (D k - n ψ k) ^ 2 / (n ψ k)`. -/
lemma sum_mul_log_inv_sub_le {s : Finset ℕ} (D : ℕ → ℕ) (hD : ∑ k ∈ s, D k = n) {ψ : ℕ → ℝ}
    (hψ : ∀ k ∈ s, 0 < ψ k) (hψ₁ : ∑ k ∈ s, ψ k = 1) :
    ∑ k ∈ s, D k * log (ψ k)⁻¹ - ∑ k ∈ s, (D k - n * ψ k) ^ 2 / (n * ψ k) ≤
      ∑ k ∈ s, D k * log (n / D k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 (k : ℕ) (hk : k ∈ s) : (D k : ℝ) = 0 := by simp [(sum_eq_zero_iff.1 hD) k hk]
    rw [sum_eq_zero fun k hk ↦ by rw [h0 k hk, zero_mul],
      sum_eq_zero fun k hk ↦ by simp [h0 k hk], sum_eq_zero fun k hk ↦ by rw [h0 k hk, zero_mul]]
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm (k : ℕ) (hk : k ∈ s) : D k * log (ψ k)⁻¹ - (D k - n * ψ k) ^ 2 / (n * ψ k) -
      (D k - n * ψ k) ≤ D k * log (n / D k) := by
    have hnψ : 0 < n * ψ k := mul_pos hn' (hψ k hk)
    have hψk := (hψ k hk).ne'
    rcases Nat.eq_zero_or_pos (D k) with h0 | hpos
    · simp only [h0, CharP.cast_eq_zero, zero_mul, zero_sub, even_two, Even.neg_pow, div_zero,
        log_zero, mul_zero]
      rw [sq, mul_div_assoc, div_self hnψ.ne', mul_one]
      linarith
    · have hpos' : (0 : ℝ) < D k := by exact_mod_cast hpos
      have hlog := one_sub_inv_le_log_of_pos (div_pos hnψ hpos')
      rw [log_div hnψ.ne' hpos'.ne', log_mul hn'.ne' (hψ k hk).ne', inv_div] at hlog
      rw [log_div hn'.ne' hpos'.ne', log_inv]
      have : D k * (1 - D k / (n * ψ k)) ≤ D k * (log n + log (ψ k) - log (D k)) :=
        mul_le_mul_of_nonneg_left hlog hpos'.le
      have hid : (D k : ℝ) * (1 - D k / (n * ψ k)) =
          -((D k - n * ψ k) ^ 2 / (n * ψ k)) - (D k - n * ψ k) := by
        field_simp
        ring
      linarith
  have hY : ∑ k ∈ s, ((D k : ℝ) - n * ψ k) = 0 := by
    rw [sum_sub_distrib, ← mul_sum, hψ₁, mul_one, sub_eq_zero]
    exact_mod_cast hD
  have := sum_le_sum hterm
  rwa [sum_sub_distrib, hY, sub_zero, sum_sub_distrib] at this

/-- **Lower bound for the size of a type class.** If the value `k ≤ N` appears `D k` times in
`a : Fin n → ℕ` and `ψ` is a positive probability vector on `[0, N]`, then the logarithm of the
size of the type class of `a` is at least
`∑ k, D k * log (1 / ψ k) - ∑ k, (D k - n ψ k) ^ 2 / (n ψ k) - (N + 1) (1 + log (n + 1))`. -/
lemma le_log_card_typeClass (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) {ψ : ℕ → ℝ}
    (hψ : ∀ k ∈ range (N + 1), 0 < ψ k) (hψ₁ : ∑ k ∈ range (N + 1), ψ k = 1) :
    ∑ k ∈ range (N + 1), #{r | a r = k} * log (ψ k)⁻¹ -
        ∑ k ∈ range (N + 1), (#{r | a r = k} - n * ψ k) ^ 2 / (n * ψ k) -
        (N + 1) * (1 + log (n + 1)) ≤ log #(typeClass a) := by
  have hD : ∑ k ∈ range (N + 1), #{r | a r = k} = n := by
    have := card_eq_sum_card_fiberwise (s := univ) (t := range (N + 1)) (f := a)
      fun r _ ↦ mem_range.2 (by grind [ha r])
    rw [card_univ, Fintype.card_fin] at this
    exact this.symm
  have hW : (#(typeClass a) : ℝ) =
      n.factorial / ∏ k ∈ range (N + 1), ((#{r | a r = k}).factorial : ℝ) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast card_typeClass_mul_prod_factorial a ha
  have hlog : log #(typeClass a) =
      log n.factorial - ∑ k ∈ range (N + 1), log (#{r | a r = k}).factorial := by
    rw [hW, log_div (by positivity) (by positivity), log_prod fun k _ ↦ by positivity]
  have h₁ := sum_mul_log_div_sub_le_log (s := range (N + 1)) (fun k ↦ #{r | a r = k}) hD
  have h₂ := sum_mul_log_inv_sub_le (s := range (N + 1)) (fun k ↦ #{r | a r = k}) hD hψ hψ₁
  rw [card_range] at h₁
  push_cast at h₁
  rw [hlog]
  linarith

end ArithmeticTriangleRemovalInVectorSpaces
