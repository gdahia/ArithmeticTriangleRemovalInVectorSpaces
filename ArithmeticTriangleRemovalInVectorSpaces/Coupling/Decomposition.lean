/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.Coupling.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Decomposition into simple triples

Three weights on `[0, N]` with equal masses whose first moments sum to `2 N` times the mass are a
nonnegative combination of simple triples: two point masses and a combination of two point masses.
This is Lemma 2.1 of Pebody. Applying `hat` to the simple triples gives the triples handled in
`ArithmeticTriangleRemovalInVectorSpaces.compatible_unif_mix`, so the `hat` of a balanced triple of
weights is compatible.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.IsWeight N w`: `w` is nonnegative and vanishes beyond
  `N`.
* `ArithmeticTriangleRemovalInVectorSpaces.IsBalanced N w₁ w₂ w₃`: the weights have equal masses
  and their first moments sum to `2 N` times the mass.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.IsBalanced.compatible_hat`: the `hat` of a balanced
  triple of weights is compatible, given Pebody's theorem at lower levels.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- A weight on `[0, N]`: a nonnegative function vanishing beyond `N`. -/
structure IsWeight (N : ℕ) (w : ℕ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ w k
  eq_zero : ∀ k, N < k → w k = 0

/-- Three weights on `[0, N]` with equal masses whose first moments sum to `2 N` times the mass. -/
structure IsBalanced (N : ℕ) (w₁ w₂ w₃ : ℕ → ℝ) : Prop where
  isWeight₁ : IsWeight N w₁
  isWeight₂ : IsWeight N w₂
  isWeight₃ : IsWeight N w₃
  mass₂ : mass N w₂ = mass N w₁
  mass₃ : mass N w₃ = mass N w₁
  moment : moment N w₁ + moment N w₂ + moment N w₃ = 2 * N * mass N w₁

/-- `σ` is a weight of mass one and first moment `μ` whose support lies in the support of `w`. -/
structure IsUnitBelow (N : ℕ) (w σ : ℕ → ℝ) (μ : ℝ) : Prop where
  isWeight : IsWeight N σ
  mass_eq : mass N σ = 1
  moment_eq : moment N σ = μ
  support : ∀ k, σ k ≠ 0 → w k ≠ 0

/-- The number of points of `[0, N]` where `w` does not vanish. -/
noncomputable def supportCard (N : ℕ) (w : ℕ → ℝ) : ℕ :=
  #{k ∈ range (N + 1) | w k ≠ 0}

variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}

lemma IsWeight.hat_eq_zero (hw : IsWeight N w) (h0 : mass N w = 0) : hat N w = 0 := by
  ext j
  apply sum_eq_zero
  intro k hk
  rw [(sum_eq_zero_iff_of_nonneg fun k _ ↦ hw.nonneg k).1 h0 k hk, zero_mul]

/-- A weight of positive mass has points of its support on both sides of its mean. -/
lemma IsWeight.exists_le_moment_le (hw : IsWeight N w) (hM : mass N w ≠ 0) :
    (∃ a ≤ N, w a ≠ 0 ∧ a * mass N w ≤ moment N w) ∧
      ∃ b ≤ N, w b ≠ 0 ∧ moment N w ≤ b * mass N w := by
  set s := {k ∈ range (N + 1) | w k ≠ 0}
  obtain ⟨k, hk, hwk⟩ := exists_ne_zero_of_sum_ne_zero hM
  have hs : s.Nonempty := ⟨k, mem_filter.2 ⟨hk, hwk⟩⟩
  have heq : ∑ k ∈ s, w k * (k * mass N w) = ∑ k ∈ s, w k * moment N w := by
    simp only [mass, moment]
    rw [sum_filter_of_ne fun k _ h ↦ left_ne_zero_of_mul h,
      sum_filter_of_ne fun k _ h ↦ left_ne_zero_of_mul h]
    simp_rw [mul_left_comm (w _), ← mul_assoc, ← sum_mul]
    ring
  have hpos {a : ℕ} (ha : a ∈ s) : 0 < w a := by
    simp only [s, mem_filter] at ha
    exact lt_of_le_of_ne (hw.nonneg a) (Ne.symm ha.2)
  obtain ⟨a, ha, hle⟩ := exists_le_of_sum_le hs heq.le
  obtain ⟨b, hb, hge⟩ := exists_le_of_sum_le hs heq.ge
  have ha' := ha
  have hb' := hb
  simp only [s, mem_filter, mem_range] at ha' hb'
  exact ⟨⟨a, by grind, ha'.2, le_of_mul_le_mul_left hle (hpos ha)⟩,
    ⟨b, by grind, hb'.2, le_of_mul_le_mul_left hge (hpos hb)⟩⟩

lemma isUnitBelow_single {c : ℕ} (hc : c ≤ N) (hw : w c ≠ 0) :
    IsUnitBelow N w (Pi.single c 1) c where
  isWeight := ⟨Pi.single_nonneg.2 zero_le_one, fun _ hk ↦ Pi.single_eq_of_ne (by grind) _⟩
  mass_eq := by simp [mass, Nat.lt_succ_of_le hc]
  moment_eq := by simp [moment, Pi.single_apply, Nat.lt_succ_of_le hc]
  support k hk := by
    obtain rfl : k = c := by
      by_contra h
      exact hk (Pi.single_eq_of_ne h _)
    exact hw

lemma isUnitBelow_mix {y z : ℕ} (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hwy : w y ≠ 0) (hwz : w z ≠ 0) :
    IsUnitBelow N w (α • (Pi.single y 1 : ℕ → ℝ) + (1 - α) • (Pi.single z 1 : ℕ → ℝ))
      (α * y + (1 - α) * z) := by
  have hy' := isUnitBelow_single hy hwy
  have hz' := isUnitBelow_single hz hwz
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k
    exact add_nonneg (mul_nonneg hα₀ (hy'.isWeight.nonneg k))
      (mul_nonneg (by linarith) (hz'.isWeight.nonneg k))
  · intro k hk
    simp [hy'.isWeight.eq_zero k hk, hz'.isWeight.eq_zero k hk]
  · rw [mass_add, mass_smul, mass_smul, hy'.mass_eq, hz'.mass_eq]
    ring
  · rw [moment_add, moment_smul, moment_smul, hy'.moment_eq, hz'.moment_eq]
  · intro k hk hwk
    apply hk
    have hyk : (Pi.single y 1 : ℕ → ℝ) k = 0 := by
      by_contra h
      exact hy'.support k h hwk
    have hzk : (Pi.single z 1 : ℕ → ℝ) k = 0 := by
      by_contra h
      exact hz'.support k h hwk
    simp [hyk, hzk]

lemma IsUnitBelow.mass_sub (hσ : IsUnitBelow N w σ μ) : mass N (w - p • σ) = mass N w - p := by
  have h : mass N (w - p • σ) = mass N w - p * mass N σ := by
    simp [mass, sum_sub_distrib, mul_sum]
  rw [h, hσ.mass_eq, mul_one]

lemma IsUnitBelow.moment_sub (hσ : IsUnitBelow N w σ μ) :
    moment N (w - p • σ) = moment N w - p * μ := by
  rw [← hσ.moment_eq]
  simp only [moment, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, sum_sub_distrib, mul_sum]
  congr with k
  ring

/-- The largest multiple of `σ` below `w` touches `w` at a point of the support of `σ`. -/
lemma IsUnitBelow.exists_ratio (hσ : IsUnitBelow N w σ μ) (hw : IsWeight N w) :
    ∃ r > 0, (∀ k, r * σ k ≤ w k) ∧ ∃ k ≤ N, σ k ≠ 0 ∧ r * σ k = w k := by
  set s := {k ∈ range (N + 1) | σ k ≠ 0}
  obtain ⟨k, hk, hσk⟩ :=
    exists_ne_zero_of_sum_ne_zero (by rw [← mass, hσ.mass_eq]; exact one_ne_zero)
  have hs : s.Nonempty := ⟨k, mem_filter.2 ⟨hk, hσk⟩⟩
  have hσpos {k : ℕ} (hσk : σ k ≠ 0) : 0 < σ k :=
    lt_of_le_of_ne (hσ.isWeight.nonneg k) (Ne.symm hσk)
  have hmem {k : ℕ} (hσk : σ k ≠ 0) : k ∈ s := by
    refine mem_filter.2 ⟨mem_range.2 ?_, hσk⟩
    by_contra h
    exact hσk (hσ.isWeight.eq_zero k (by grind))
  obtain ⟨k₀, hk₀, heq⟩ := exists_mem_eq_inf' hs fun k ↦ w k / σ k
  simp only [s, mem_filter, mem_range] at hk₀
  obtain ⟨hk₀N, hσk₀⟩ := hk₀
  refine ⟨s.inf' hs fun k ↦ w k / σ k, ?_, ?_, k₀, by grind, hσk₀, ?_⟩
  · rw [gt_iff_lt, lt_inf'_iff]
    intro k hk
    simp only [s, mem_filter] at hk
    obtain ⟨-, hσk⟩ := hk
    exact div_pos (lt_of_le_of_ne (hw.nonneg k) (Ne.symm (hσ.support k hσk))) (hσpos hσk)
  · intro k
    by_cases hσk : σ k = 0
    · rw [hσk, mul_zero]
      exact hw.nonneg k
    · rw [← le_div_iff₀ (hσpos hσk)]
      exact inf'_le _ (hmem hσk)
  · rw [heq]
    field_simp [hσk₀]

lemma IsUnitBelow.support_sub_subset (hσ : IsUnitBelow N w σ μ) :
    {k ∈ range (N + 1) | (w - p • σ) k ≠ 0} ⊆ {k ∈ range (N + 1) | w k ≠ 0} := by
  intro k
  simp only [mem_filter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rintro ⟨hk, hne⟩
  refine ⟨hk, ?_⟩
  intro hwk
  apply hne
  have hσk : σ k = 0 := by
    by_contra h
    exact hσ.support k h hwk
  simp [hwk, hσk]

lemma IsUnitBelow.supportCard_sub_le (hσ : IsUnitBelow N w σ μ) :
    supportCard N (w - p • σ) ≤ supportCard N w :=
  card_le_card hσ.support_sub_subset

lemma IsUnitBelow.supportCard_sub_lt (hσ : IsUnitBelow N w σ μ) {k : ℕ} (hk : k ≤ N)
    (hσk : σ k ≠ 0) (hpk : p * σ k = w k) : supportCard N (w - p • σ) < supportCard N w := by
  refine card_lt_card ((ssubset_iff_of_subset hσ.support_sub_subset).2 ⟨k, ?_, ?_⟩)
  · simp only [mem_filter, mem_range]
    exact ⟨by grind, hσ.support k hσk⟩
  · simp [hpk]

lemma IsWeight.sub (hw : IsWeight N w) (hσ : IsWeight N σ) (hle : ∀ k, p * σ k ≤ w k) :
    IsWeight N (w - p • σ) :=
  ⟨fun k ↦ sub_nonneg.2 (hle k), fun k hk ↦ by simp [hw.eq_zero k hk, hσ.eq_zero k hk]⟩

lemma IsBalanced.sub (hb : IsBalanced N w₁ w₂ w₃) (h₁ : IsUnitBelow N w₁ σ₁ μ₁)
    (h₂ : IsUnitBelow N w₂ σ₂ μ₂) (h₃ : IsUnitBelow N w₃ σ₃ μ₃) (hμ : μ₁ + μ₂ + μ₃ = 2 * N)
    (hle₁ : ∀ k, p * σ₁ k ≤ w₁ k) (hle₂ : ∀ k, p * σ₂ k ≤ w₂ k) (hle₃ : ∀ k, p * σ₃ k ≤ w₃ k) :
    IsBalanced N (w₁ - p • σ₁) (w₂ - p • σ₂) (w₃ - p • σ₃) where
  isWeight₁ := hb.isWeight₁.sub h₁.isWeight hle₁
  isWeight₂ := hb.isWeight₂.sub h₂.isWeight hle₂
  isWeight₃ := hb.isWeight₃.sub h₃.isWeight hle₃
  mass₂ := by rw [h₂.mass_sub, h₁.mass_sub, hb.mass₂]
  mass₃ := by rw [h₃.mass_sub, h₁.mass_sub, hb.mass₃]
  moment := by
    rw [h₁.moment_sub, h₂.moment_sub, h₃.moment_sub, h₁.mass_sub]
    linear_combination hb.moment - p * hμ

lemma IsBalanced.comm₂₃ (hb : IsBalanced N w₁ w₂ w₃) : IsBalanced N w₁ w₃ w₂ :=
  ⟨hb.isWeight₁, hb.isWeight₃, hb.isWeight₂, hb.mass₃, hb.mass₂, by linarith [hb.moment]⟩

lemma IsBalanced.comm₁₃ (hb : IsBalanced N w₁ w₂ w₃) : IsBalanced N w₃ w₂ w₁ :=
  ⟨hb.isWeight₃, hb.isWeight₂, hb.isWeight₁, hb.mass₂.trans hb.mass₃.symm, hb.mass₃.symm,
    by rw [hb.mass₃]; linarith [hb.moment]⟩

/-- Subtracting the largest multiple of a compatible triple of unit weights lowers the total
support size, so the induction hypothesis applies to what is left. -/
lemma IsBalanced.compatible_hat_of_isUnitBelow (hb : IsBalanced N w₁ w₂ w₃)
    (h₁ : IsUnitBelow N w₁ σ₁ μ₁) (h₂ : IsUnitBelow N w₂ σ₂ μ₂) (h₃ : IsUnitBelow N w₃ σ₃ μ₃)
    (hμ : μ₁ + μ₂ + μ₃ = 2 * N) (hs : Compatible N (hat N σ₁) (hat N σ₂) (hat N σ₃))
    (IH : ∀ v₁ v₂ v₃, IsBalanced N v₁ v₂ v₃ →
      supportCard N v₁ + supportCard N v₂ + supportCard N v₃ <
        supportCard N w₁ + supportCard N w₂ + supportCard N w₃ →
      Compatible N (hat N v₁) (hat N v₂) (hat N v₃)) :
    Compatible N (hat N w₁) (hat N w₂) (hat N w₃) := by
  obtain ⟨r₁, hr₁, hle₁, k₁, hk₁, hσk₁, heq₁⟩ := h₁.exists_ratio hb.isWeight₁
  obtain ⟨r₂, hr₂, hle₂, k₂, hk₂, hσk₂, heq₂⟩ := h₂.exists_ratio hb.isWeight₂
  obtain ⟨r₃, hr₃, hle₃, k₃, hk₃, hσk₃, heq₃⟩ := h₃.exists_ratio hb.isWeight₃
  set p := min (min r₁ r₂) r₃
  have hle (r : ℝ) (σ w : ℕ → ℝ) (hpr : p ≤ r) (hσ : ∀ k, 0 ≤ σ k) (hle : ∀ k, r * σ k ≤ w k)
      (k : ℕ) : p * σ k ≤ w k := by
    grw [hpr]
    · exact hle k
    · exact hσ k
  have hcomp := (IH _ _ _ (hb.sub h₁ h₂ h₃ hμ (hle r₁ σ₁ w₁ (by simp [p]) h₁.isWeight.nonneg hle₁)
    (hle r₂ σ₂ w₂ (by simp [p]) h₂.isWeight.nonneg hle₂)
    (hle r₃ σ₃ w₃ (by simp [p]) h₃.isWeight.nonneg hle₃)) ?_).add
    (hs.smul (by positivity : 0 ≤ p))
  · simpa only [← hat_smul, ← hat_add, sub_add_cancel] using hcomp
  have hle₁' := h₁.supportCard_sub_le (p := p)
  have hle₂' := h₂.supportCard_sub_le (p := p)
  have hle₃' := h₃.supportCard_sub_le (p := p)
  obtain hp | hp | hp : p = r₁ ∨ p = r₂ ∨ p = r₃ := by
    simp only [p]
    grind
  · have := h₁.supportCard_sub_lt hk₁ hσk₁ (hp ▸ heq₁)
    grind
  · have := h₂.supportCard_sub_lt hk₂ hσk₂ (hp ▸ heq₂)
    grind
  · have := h₃.supportCard_sub_lt hk₃ hσk₃ (hp ▸ heq₃)
    grind

lemma exists_mix {c d y z : ℕ} (h₁ : c + d + y ≤ 2 * N) (h₂ : 2 * N ≤ c + d + z) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ (c + d + α * y + (1 - α) * z : ℝ) = 2 * N := by
  rcases eq_or_lt_of_le (by grind : y ≤ z) with rfl | hyz
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    norm_num
    exact_mod_cast (by grind : c + d + y = 2 * N)
  · have hyz' : (y : ℝ) < z := by exact_mod_cast hyz
    have h₁' : (c + d + y : ℝ) ≤ 2 * N := by exact_mod_cast h₁
    have h₂' : (2 * N : ℝ) ≤ c + d + z := by exact_mod_cast h₂
    refine ⟨(c + d + z - 2 * N) / (z - y), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
    · rw [div_le_one (by linarith)]
      linarith
    · field_simp
      ring

/-- The step of the decomposition where the mixed point masses sit in the third weight. -/
lemma IsBalanced.compatible_hat_of_mix (ih : ∀ m < N, DecreasingCompatible m)
    (hb : IsBalanced N w₁ w₂ w₃) {n : ℕ}
    (hn : supportCard N w₁ + supportCard N w₂ + supportCard N w₃ ≤ n)
    (IH : ∀ m < n, ∀ v₁ v₂ v₃, IsBalanced N v₁ v₂ v₃ →
      supportCard N v₁ + supportCard N v₂ + supportCard N v₃ ≤ m →
      Compatible N (hat N v₁) (hat N v₂) (hat N v₃))
    {c d y z : ℕ} (hc : c ≤ N) (hd : d ≤ N) (hy : y ≤ N) (hz : z ≤ N) (hwc : w₁ c ≠ 0)
    (hwd : w₂ d ≠ 0) (hwy : w₃ y ≠ 0) (hwz : w₃ z ≠ 0) (h₁ : c + d + y ≤ 2 * N)
    (h₂ : 2 * N ≤ c + d + z) : Compatible N (hat N w₁) (hat N w₂) (hat N w₃) := by
  obtain ⟨α, hα₀, hα₁, hsum⟩ := exists_mix h₁ h₂
  refine hb.compatible_hat_of_isUnitBelow (isUnitBelow_single hc hwc) (isUnitBelow_single hd hwd)
    (isUnitBelow_mix hy hz hα₀ hα₁ hwy hwz) (by linarith) ?_ ?_
  · rw [hat_single hc, hat_single hd, hat_add, hat_smul, hat_smul, hat_single hy, hat_single hz]
    exact compatible_unif_mix ih hc hd hy hz hα₀ hα₁ hsum
  · intro v₁ v₂ v₃ hv hlt
    exact IH _ (by grind) _ _ _ hv le_rfl

lemma IsBalanced.compatible_hat_of_le (ih : ∀ m < N, DecreasingCompatible m)
    (hb : IsBalanced N w₁ w₂ w₃) (n : ℕ)
    (hn : supportCard N w₁ + supportCard N w₂ + supportCard N w₃ ≤ n) :
    Compatible N (hat N w₁) (hat N w₂) (hat N w₃) := by
  induction n using Nat.strong_induction_on generalizing w₁ w₂ w₃ with
  | _ n IH =>
  by_cases hM : mass N w₁ = 0
  · rw [hb.isWeight₁.hat_eq_zero hM, hb.isWeight₂.hat_eq_zero (hb.mass₂.trans hM),
      hb.isWeight₃.hat_eq_zero (hb.mass₃.trans hM)]
    exact compatible_zero
  obtain ⟨⟨a₁, ha₁, hwa₁, hla₁⟩, ⟨b₁, hb₁, hwb₁, hlb₁⟩⟩ := hb.isWeight₁.exists_le_moment_le hM
  obtain ⟨⟨a₂, ha₂, hwa₂, hla₂⟩, ⟨b₂, hb₂, hwb₂, hlb₂⟩⟩ :=
    hb.isWeight₂.exists_le_moment_le (by rwa [hb.mass₂])
  obtain ⟨⟨a₃, ha₃, hwa₃, hla₃⟩, ⟨b₃, hb₃, hwb₃, hlb₃⟩⟩ :=
    hb.isWeight₃.exists_le_moment_le (by rwa [hb.mass₃])
  rw [hb.mass₂] at hla₂ hlb₂
  rw [hb.mass₃] at hla₃ hlb₃
  have hMpos : 0 < mass N w₁ :=
    lt_of_le_of_ne (sum_nonneg fun k _ ↦ hb.isWeight₁.nonneg k) (Ne.symm hM)
  have hA : a₁ + a₂ + a₃ ≤ 2 * N := by
    have : ((a₁ + a₂ + a₃ : ℕ) : ℝ) * mass N w₁ ≤ (2 * N : ℕ) * mass N w₁ := by
      push_cast
      linarith [hb.moment]
    exact_mod_cast le_of_mul_le_mul_right this hMpos
  have hB : 2 * N ≤ b₁ + b₂ + b₃ := by
    have : ((2 * N : ℕ) : ℝ) * mass N w₁ ≤ (b₁ + b₂ + b₃ : ℕ) * mass N w₁ := by
      push_cast
      linarith [hb.moment]
    exact_mod_cast le_of_mul_le_mul_right this hMpos
  by_cases h₁ : 2 * N ≤ a₁ + a₂ + b₃
  · exact hb.compatible_hat_of_mix ih hn IH ha₁ ha₂ ha₃ hb₃ hwa₁ hwa₂ hwa₃ hwb₃ hA h₁
  by_cases h₂ : 2 * N ≤ a₁ + b₂ + b₃
  · exact (hb.comm₂₃.compatible_hat_of_mix ih (by grind) IH ha₁ hb₃ ha₂ hb₂ hwa₁ hwb₃ hwa₂ hwb₂
      (by grind) (by grind)).comm₂₃
  · exact (hb.comm₁₃.compatible_hat_of_mix ih (by grind) IH hb₃ hb₂ ha₁ hb₁ hwb₃ hwb₂ hwa₁ hwb₁
      (by grind) (by grind)).comm₁₃

/-- **Lemma 2.1 of Pebody, after applying `hat`.** The `hat` of a balanced triple of weights is
compatible, given Pebody's theorem at lower levels. -/
lemma IsBalanced.compatible_hat (ih : ∀ m < N, DecreasingCompatible m)
    (hb : IsBalanced N w₁ w₂ w₃) : Compatible N (hat N w₁) (hat N w₂) (hat N w₃) :=
  hb.compatible_hat_of_le ih _ le_rfl

end ArithmeticTriangleRemovalInVectorSpaces
