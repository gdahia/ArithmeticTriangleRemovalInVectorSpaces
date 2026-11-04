/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.Coupling.Peeling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform distributions and their mixtures

Every decreasing mass function on `[0, N]` is a nonnegative combination of the uniform
distributions `unif k` on `[0, k]`, `k ≤ N`. This file proves that `unif k₁`, `unif k₂` and a
mixture of `unif y` and `unif z` are compatible when their means sum to `N`, assuming Pebody's
theorem at lower levels. This is the case analysis at the end of Pebody's proof.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.unif k`: the uniform distribution on `[0, k]`.
* `ArithmeticTriangleRemovalInVectorSpaces.hat N w`: the combination `∑ k ≤ N, w k • unif k`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_hat`: a decreasing mass function is a
  nonnegative combination of uniform distributions.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_lastcase`: Corollary 5.2 of Pebody.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_unif_mix`: `unif k₁`, `unif k₂` and
  `α • unif y + (1 - α) • unif z` are compatible when their means sum to `N`.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The uniform distribution on `[0, k]`. -/
@[expose] noncomputable def unif (k j : ℕ) : ℝ :=
  if j ≤ k then ((k : ℝ) + 1)⁻¹ else 0

/-- The combination `∑ k ≤ N, w k • unif k` of uniform distributions. -/
@[expose] noncomputable def hat (N : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), w k * unif k j

variable {N k : ℕ} {π π' : ℕ → ℝ}

lemma IsDecreasingOn.add (h : IsDecreasingOn N π) (h' : IsDecreasingOn N π') :
    IsDecreasingOn N (π + π') :=
  ⟨fun k ↦ add_nonneg (h.nonneg k) (h'.nonneg k), h.antitone.add h'.antitone,
    by simp [h.eq_zero, h'.eq_zero]⟩

lemma IsDecreasingOn.smul (h : IsDecreasingOn N π) {r : ℝ} (hr : 0 ≤ r) :
    IsDecreasingOn N (r • π) :=
  ⟨fun k ↦ mul_nonneg hr (h.nonneg k), fun _ _ hab ↦ mul_le_mul_of_nonneg_left (h.antitone hab) hr,
    by simp [h.eq_zero]⟩

lemma mass_add : mass N (π + π') = mass N π + mass N π' := by
  simp [mass, sum_add_distrib]

lemma mass_smul (r : ℝ) : mass N (r • π) = r * mass N π := by
  simp [mass, mul_sum]

lemma moment_add : moment N (π + π') = moment N π + moment N π' := by
  simp [moment, mul_add, sum_add_distrib]

lemma moment_smul (r : ℝ) : moment N (r • π) = r * moment N π := by
  simp only [moment, Pi.smul_apply, smul_eq_mul, mul_sum]
  congr with k
  ring

lemma isDecreasingOn_unif (hk : k ≤ N) : IsDecreasingOn N (unif k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold unif
    positivity
  · intro a b hab
    unfold unif
    grind [(by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹)]
  · simp only [unif, ite_eq_right_iff]
    grind

lemma unif_eq_zero (hk : k < N) : unif k N = 0 := by
  simp only [unif, ite_eq_right_iff]
  grind

lemma sum_mul_unif (hk : k ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ range (N + 1), f j * unif k j = (∑ j ∈ range (k + 1), f j) / (k + 1) := by
  rw [← sum_range_add_sum_Ico _ (by grind : k + 1 ≤ N + 1), sum_eq_zero (s := Ico _ _),
    add_zero, div_eq_mul_inv, sum_mul]
  · rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    congr with j
    simp [unif, j.is_le]
  · intro j hj
    simp only [mem_Ico] at hj
    simp [unif, (by grind : ¬j ≤ k)]

lemma mass_unif (hk : k ≤ N) : mass N (unif k) = 1 := by
  have h := sum_mul_unif hk fun _ ↦ 1
  simp only [one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  rw [mass, h]
  push_cast
  field_simp

lemma sum_range_succ_cast (k : ℕ) : ∑ j ∈ range (k + 1), (j : ℝ) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma moment_unif (hk : k ≤ N) : moment N (unif k) = k / 2 := by
  rw [moment, sum_mul_unif hk, sum_range_succ_cast]
  field_simp

lemma isDecreasingOn_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) : IsDecreasingOn N (α • unif y + (1 - α) • unif z) :=
  ((isDecreasingOn_unif hy).smul hα₀).add ((isDecreasingOn_unif hz).smul (by linarith))

lemma mass_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) (α : ℝ) :
    mass N (α • unif y + (1 - α) • unif z) = 1 := by
  rw [mass_add, mass_smul, mass_smul, mass_unif hy, mass_unif hz]
  ring

lemma moment_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) (α : ℝ) :
    moment N (α • unif y + (1 - α) • unif z) = (α * y + (1 - α) * z) / 2 := by
  rw [moment_add, moment_smul, moment_smul, moment_unif hy, moment_unif hz]
  ring

lemma mix_eq_zero {y z : ℕ} {α : ℝ} (hy : y < N ∨ α = 0) (hz : z < N ∨ α = 1) :
    (α • unif y + (1 - α) • unif z) N = 0 := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases hy with hy | rfl <;> rcases hz with hz | hz
  all_goals first
    | simp [unif_eq_zero hy, unif_eq_zero hz]
    | simp [unif_eq_zero hy, hz]
    | simp [unif_eq_zero hz]
    | simp_all

lemma hat_add (w w' : ℕ → ℝ) : hat N (w + w') = hat N w + hat N w' := by
  ext j
  simp [hat, add_mul, sum_add_distrib]

lemma hat_smul (r : ℝ) (w : ℕ → ℝ) : hat N (r • w) = r • hat N w := by
  ext j
  simp [hat, mul_sum, mul_assoc]

lemma hat_zero : hat N 0 = 0 := by
  ext j
  simp [hat]

lemma hat_single (hk : k ≤ N) : hat N (Pi.single k 1) = unif k := by
  ext j
  rw [hat, sum_eq_single_of_mem k (mem_range.2 (by grind)) fun b _ hb ↦ by simp [hb]]
  simp

lemma mass_hat (w : ℕ → ℝ) : mass N (hat N w) = ∑ k ∈ range (N + 1), w k := by
  simp only [mass, hat]
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  congr with k
  rw [← mul_sum, ← mass, mass_unif k.is_le, mul_one]

lemma moment_hat (w : ℕ → ℝ) :
    moment N (hat N w) = (∑ k ∈ range (N + 1), (k : ℝ) * w k) / 2 := by
  simp only [moment, hat, mul_sum]
  rw [sum_comm, div_eq_mul_inv, sum_mul, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  congr with k
  simp_rw [mul_left_comm _ (w k), ← mul_sum]
  rw [← moment, moment_unif k.is_le]
  ring

/-- **A decreasing mass function is a combination of uniform distributions**, with the
nonnegative weights `(k + 1) * (π k - π (k + 1))`. -/
lemma IsDecreasingOn.eq_hat (h : IsDecreasingOn N π) :
    π = hat N fun k ↦ (k + 1) * (π k - π (k + 1)) := by
  ext j
  have hterm (k : ℕ) : (k + 1 : ℝ) * (π k - π (k + 1)) * unif k j =
      if j ≤ k then π k - π (k + 1) else 0 := by
    unfold unif
    grind
  simp only [hat, hterm]
  by_cases hj : j ≤ N
  · rw [← sum_range_add_sum_Ico _ (by grind : j ≤ N + 1), sum_eq_zero fun k hk ↦ by grind,
      zero_add, sum_Ico_eq_sum_range]
    simp only [le_add_iff_nonneg_right, zero_le, ite_true, add_assoc j]
    rw [sum_range_sub' (fun k ↦ π (j + k)), add_zero, (by grind : j + (N + 1 - j) = N + 1),
      h.eq_zero, sub_zero]
  · rw [h.eq_zero_of_lt (by grind)]
    exact (sum_eq_zero fun k hk ↦ by grind).symm

lemma IsDecreasingOn.weight_nonneg (h : IsDecreasingOn N π) (k : ℕ) :
    0 ≤ (k + 1 : ℝ) * (π k - π (k + 1)) :=
  mul_nonneg (by positivity) (sub_nonneg.2 (h.antitone (Nat.le_succ k)))

lemma IsDecreasingOn.weight_eq_zero (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) :
    (k + 1 : ℝ) * (π k - π (k + 1)) = 0 := by
  rw [h.eq_zero_of_lt hk, h.eq_zero_of_lt (by grind), sub_zero, mul_zero]

/-- The triples `(0, b, N - b)` with `b` uniform on `[0, N]`. -/
lemma compatible_unif_zero : Compatible N (unif 0) (unif N) (unif N) := by
  convert compatible_layer (N := N) (f := fun _ ↦ ((N : ℝ) + 1)⁻¹) (fun _ ↦ by positivity)
    using 1
  · ext a
    simp only [unif, nonpos_iff_eq_zero, CharP.cast_eq_zero, zero_add, inv_one, sum_const,
      card_range, nsmul_eq_mul]
    push_cast
    grind
  · ext b
    rfl
  · ext c
    simp only [unif]

/-- Three uniform distributions whose means sum to the level `a + b` are compatible, given
Pebody's theorem at that level. -/
lemma compatible_unif_triple {a b : ℕ} (h : DecreasingCompatible (a + b)) :
    Compatible (a + b) (unif a) (unif b) (unif (a + b)) := by
  refine h _ _ _ (isDecreasingOn_unif (by grind)) (isDecreasingOn_unif (by grind))
    (isDecreasingOn_unif le_rfl) (by rw [mass_unif (by grind), mass_unif (by grind)])
    (by rw [mass_unif le_rfl, mass_unif (by grind)]) ?_
  rw [moment_unif (by grind), moment_unif (by grind), moment_unif le_rfl, mass_unif (by grind)]
  push_cast
  ring

/-- **Corollary 5.2 of Pebody.** For `i > 0`, the distributions `unif i`, `unif N` and the mixture
of `unif j` and `unif N` with mean `(N - i) / 2` are compatible, where `N = i + j + r + 1`. -/
lemma compatible_lastcase {i j r : ℕ} (hij : DecreasingCompatible (i + j))
    (hir : DecreasingCompatible (i + r)) :
    Compatible (i + j + r + 1) (unif i) (unif (i + j + r + 1))
      (((i : ℝ) / (i + r + 1)) • unif j + (1 - (i : ℝ) / (i + r + 1)) • unif (i + j + r + 1)) := by
  have hw₀ : (0 : ℝ) ≤ (i + j + 1) / (i + j + r + 2) := by positivity
  have hw₁ : (0 : ℝ) ≤ 1 - (i + j + 1) / (i + j + r + 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have h₁ := ((compatible_unif_triple hij).shift (r + 1)).comm₂₃.smul hw₀
  have h₂ := ((compatible_unif_triple hir).shift (j + 1)).smul hw₁
  rw [(by grind : i + r + (j + 1) = i + j + (r + 1))] at h₂
  rw [(by grind : i + j + r + 1 = i + j + (r + 1))]
  convert h₁.add h₂ using 1
  · ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext k
    simp only [unif, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    grind
  · ext k
    simp only [unif, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    grind

/-- The case of Pebody's proof where the first distribution is `unif N` and the third one has
mass at `N`: `unif N`, `unif i` and the mixture of `unif j` and `unif N` with weight `α < 1` are
compatible when their means sum to `N`. -/
lemma compatible_top (ih : ∀ m < N, DecreasingCompatible m) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hsum : (i : ℝ) + α * j + (1 - α) * N = N) :
    Compatible N (unif N) (unif i) (α • unif j + (1 - α) • unif N) := by
  by_cases h0 : α = 0 ∨ j = N
  · have hi0 : i = 0 := by
      rcases h0 with rfl | rfl
      · exact_mod_cast (by linarith : (i : ℝ) = 0)
      · exact_mod_cast (by linarith : (i : ℝ) = 0)
    have hmix : α • unif j + (1 - α) • unif N = unif N := by
      rcases h0 with rfl | rfl
      · simp
      · rw [← add_smul]
        simp
    rw [hi0, hmix]
    exact compatible_unif_zero.comm₁₂
  push Not at h0
  obtain ⟨hα0, hjN⟩ := h0
  have hαpos : 0 < α := lt_of_le_of_ne hα₀ (Ne.symm hα0)
  have hjN' : j < N := lt_of_le_of_ne hj hjN
  have hieq : (i : ℝ) = α * (N - j) := by linarith
  have hipos : 0 < i := by
    have : (0 : ℝ) < i := by
      rw [hieq]
      exact mul_pos hαpos (by rw [sub_pos]; exact_mod_cast hjN')
    exact_mod_cast this
  have hijN : i + j < N := by
    have : (i : ℝ) < N - j := by
      rw [hieq]
      exact mul_lt_of_lt_one_left (by rw [sub_pos]; exact_mod_cast hjN') hα₁
    have : (i + j : ℝ) < N := by linarith
    exact_mod_cast this
  obtain ⟨r, rfl⟩ : ∃ r, N = i + j + r + 1 := ⟨N - i - j - 1, by grind⟩
  have hα : α = (i : ℝ) / (i + r + 1) := by
    rw [eq_div_iff (by positivity)]
    push_cast at hieq
    linarith
  rw [hα]
  exact (compatible_lastcase (ih _ (by grind)) (ih _ (by grind))).comm₁₂

/-- `unif k₁`, `unif k₂` and `α • unif y + (1 - α) • unif z` are compatible at level `N` when
their means sum to `N`, given Pebody's theorem at lower levels. -/
lemma compatible_unif_mix (ih : ∀ m < N, DecreasingCompatible m) {k₁ k₂ y z : ℕ} (hk₁ : k₁ ≤ N)
    (hk₂ : k₂ ≤ N) (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hsum : (k₁ + k₂ + α * y + (1 - α) * z : ℝ) = 2 * N) :
    Compatible N (unif k₁) (unif k₂) (α • unif y + (1 - α) • unif z) := by
  have hm := mass_mix hy hz α
  have hmom := moment_mix hy hz α
  have hd := isDecreasingOn_mix hy hz hα₀ hα₁
  rcases N with _ | n
  · obtain ⟨rfl, rfl, rfl, rfl⟩ : k₁ = 0 ∧ k₂ = 0 ∧ y = 0 ∧ z = 0 := by grind
    rw [← add_smul, add_sub_cancel, one_smul]
    exact compatible_unif_zero
  push_cast at hsum
  have hih := ih n (by grind)
  have hmk₁ := mass_unif hk₁
  have hmk₂ := mass_unif hk₂
  have hmo₁ := moment_unif hk₁
  have hmo₂ := moment_unif hk₂
  set Q := (y < n + 1 ∨ α = 0) ∧ (z < n + 1 ∨ α = 1)
  by_cases hA : k₁ < n + 1 ∧ k₂ < n + 1
  · obtain ⟨hA₁, hA₂⟩ := hA
    refine (compatible_of_eq_zero_of_eq_zero hih hd (isDecreasingOn_unif hk₁)
      (isDecreasingOn_unif hk₂) (unif_eq_zero hA₁) (unif_eq_zero hA₂) (by rw [hm, hmk₁])
      (by rw [hm, hmk₂]) ?_).comm₁₂.comm₂₃
    rw [hm, hmom, hmo₁, hmo₂]
    push_cast
    linarith
  by_cases hB : k₂ < n + 1 ∧ Q
  · obtain ⟨hB₁, hBy, hBz⟩ := hB
    refine compatible_of_eq_zero_of_eq_zero hih (isDecreasingOn_unif hk₁)
      (isDecreasingOn_unif hk₂) hd (unif_eq_zero hB₁) (mix_eq_zero hBy hBz) (by rw [hmk₁, hmk₂])
      (by rw [hm, hmk₁]) ?_
    rw [hmk₁, hmo₁, hmo₂, hmom]
    push_cast
    linarith
  by_cases hC : k₁ < n + 1 ∧ Q
  · obtain ⟨hC₁, hCy, hCz⟩ := hC
    refine (compatible_of_eq_zero_of_eq_zero hih (isDecreasingOn_unif hk₂)
      (isDecreasingOn_unif hk₁) hd (unif_eq_zero hC₁) (mix_eq_zero hCy hCz) (by rw [hmk₁, hmk₂])
      (by rw [hm, hmk₂]) ?_).comm₁₂
    rw [hmk₂, hmo₁, hmo₂, hmom]
    push_cast
    linarith
  by_cases hQ : Q
  · obtain rfl : k₁ = n + 1 := by grind
    obtain rfl : k₂ = n + 1 := by grind
    have hy0 : α * y = 0 := by
      push_cast at hsum
      linarith [mul_nonneg hα₀ y.cast_nonneg, mul_nonneg (sub_nonneg.2 hα₁) z.cast_nonneg]
    have hz0 : (1 - α) * z = 0 := by
      push_cast at hsum
      linarith [mul_nonneg hα₀ y.cast_nonneg, mul_nonneg (sub_nonneg.2 hα₁) z.cast_nonneg]
    have hmix : α • unif y + (1 - α) • unif z = unif 0 := by
      rcases mul_eq_zero.1 hy0 with rfl | hy0 <;> rcases mul_eq_zero.1 hz0 with hz0 | hz0
      · norm_num at hz0
      · simp_all
      · rw [(by linarith : α = 1)]
        simp_all
      · simp_all [← add_smul]
    rw [hmix]
    exact compatible_unif_zero.comm₁₃
  have htop (i : ℕ) (hi : i ≤ n + 1) (hsum' : (i + (n + 1) + α * y + (1 - α) * z : ℝ) =
      2 * (n + 1)) :
      Compatible (n + 1) (unif (n + 1)) (unif i) (α • unif y + (1 - α) • unif z) := by
    rcases (by grind : (y = n + 1 ∧ α ≠ 0) ∨ (z = n + 1 ∧ α ≠ 1)) with ⟨rfl, hα0⟩ | ⟨rfl, hα1⟩
    · have := compatible_top ih hi hz (α := 1 - α) (by linarith)
        (by linarith [lt_of_le_of_ne hα₀ (Ne.symm hα0)]) (by push_cast at *; linarith)
      rwa [sub_sub_cancel, add_comm ((1 - α) • unif z)] at this
    · exact compatible_top ih hi hy hα₀ (lt_of_le_of_ne hα₁ hα1) (by push_cast at *; linarith)
  rcases (by grind : k₁ = n + 1 ∨ k₂ = n + 1) with rfl | rfl
  · exact htop k₂ hk₂ (by push_cast at hsum; linarith)
  · exact (htop k₁ hk₁ (by push_cast at hsum; linarith)).comm₁₂

end ArithmeticTriangleRemovalInVectorSpaces
