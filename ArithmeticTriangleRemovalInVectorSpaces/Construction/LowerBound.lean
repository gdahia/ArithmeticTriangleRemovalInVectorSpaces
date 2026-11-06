/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.Construction.TypeClass
public import ArithmeticTriangleRemovalInVectorSpaces.Coupling.Pebody
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
import ArithmeticTriangleRemovalInVectorSpaces.Construction.Family
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.GeomSum

/-!
# Large multicolored sum-free families

Kleinberg, Sawin and Speyer showed that the exponent `1 - c p` in the bound on multicolored
sum-free families in `Fin n → ZMod p` cannot be lowered. Pebody's theorem gives a coupling `J` of
three copies of the truncated geometric distribution `geomDist N ρ` on `range (N + 1)`, with
`N = p - 1`, of mean `N / 3`. Rounding `d * J` down gives a base point whose coordinates have
empirical distributions within a bounded error of `d * geomDist N ρ`, so their type classes have
about `(ρ ^ (-N / 3) * ∑ k, ρ ^ k) ^ n ≥ p ^ ((1 - c p) * n)` elements. The sum-free family of
this base point, padded with zero coordinates, has at least `p ^ ((1 - c p - η) * n)` members for
`n ≥ sumFreeDim p η`. Taking `ρ ≥ 1 / 2` keeps the error terms explicit in `p`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.geomDist N ρ`: the truncated geometric distribution
  `k ↦ ρ ^ k / ∑ j ∈ range (N + 1), ρ ^ j`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_card_filter_mem_Icc`: rounding a coupling to a
  base point.
* `ArithmeticTriangleRemovalInVectorSpaces.le_log_card_typeClass_geomDist`: the size of a type
  class whose empirical distribution is close to a multiple of `geomDist N ρ`.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_le_log_card_typeClass`: base points with large
  type classes in every dimension `d ≥ p ^ 4 + 1`.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_rpow_le`: for every
  `η > 0` and `n ≥ sumFreeDim p η`, there is a multicolored sum-free family in `Fin n → ZMod p`
  with at least `p ^ ((1 - c p - η) * n)` members (the second part of Theorem 2 of Fox and Lovász).
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n N : ℕ} {ρ : ℝ}

/-- The truncated geometric distribution `k ↦ ρ ^ k / ∑ j ∈ range (N + 1), ρ ^ j` on
`range (N + 1)`. -/
noncomputable def geomDist (N : ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  ρ ^ k / ∑ j ∈ range (N + 1), ρ ^ j

lemma geomDist_pos (hρ : 0 < ρ) (k : ℕ) : 0 < geomDist N ρ k :=
  div_pos (pow_pos hρ k) (geom_sum_pos hρ.le N.succ_ne_zero)

lemma sum_geomDist (hρ : 0 < ρ) : ∑ k ∈ range (N + 1), geomDist N ρ k = 1 := by
  simp only [geomDist]
  rw [← sum_div, div_self (geom_sum_pos hρ.le N.succ_ne_zero).ne']

lemma geomDist_le_one (hρ : 0 < ρ) {k : ℕ} (hk : k ≤ N) : geomDist N ρ k ≤ 1 := by
  rw [geomDist, div_le_one (geom_sum_pos hρ.le N.succ_ne_zero)]
  exact single_le_sum (fun j _ ↦ by positivity) (mem_range_succ_iff.2 hk)

lemma geomDist_le_geomDist (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {k : ℕ} (hk : k ≤ N) :
    geomDist N ρ N ≤ geomDist N ρ k := by
  rw [geomDist, geomDist, div_le_div_iff_of_pos_right (geom_sum_pos hρ₀.le N.succ_ne_zero)]
  exact pow_le_pow_of_le_one hρ₀.le hρ₁.le hk

lemma log_inv_geomDist (hρ : 0 < ρ) (k : ℕ) :
    log (geomDist N ρ k)⁻¹ = log (∑ j ∈ range (N + 1), ρ ^ j) - k * log ρ := by
  rw [geomDist, inv_div, log_div (geom_sum_pos hρ.le N.succ_ne_zero).ne' (by positivity),
    log_pow]

/-- `geomDist N ρ` has mean `N / 3` if `3 * ∑ k, k * ρ ^ k = N * ∑ k, ρ ^ k`. -/
lemma sum_mul_geomDist (hρ : 0 < ρ)
    (hmean : 3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k) :
    ∑ k ∈ range (N + 1), k * geomDist N ρ k = N / 3 := by
  simp only [geomDist, mul_div_assoc', ← sum_div]
  rw [div_eq_div_iff (geom_sum_pos hρ.le N.succ_ne_zero).ne' three_ne_zero]
  linarith

/-- If each value `k ≤ N` appears in `a` between `t * μ k - T` and `t * μ k` times, then `n` lies
between `t * ∑ k, μ k - (N + 1) * T` and `t * ∑ k, μ k`. -/
lemma natCast_mem_Icc_of_card_filter_mem_Icc {a : Fin n → ℕ} (ha : ∀ r, a r ≤ N) {μ : ℕ → ℝ}
    {t T : ℝ}
    (hD : ∀ k ∈ range (N + 1), (#{r | a r = k} : ℝ) ∈ Set.Icc (t * μ k - T) (t * μ k)) :
    (n : ℝ) ∈
      Set.Icc (t * ∑ k ∈ range (N + 1), μ k - (N + 1) * T) (t * ∑ k ∈ range (N + 1), μ k) := by
  rw [← sum_card_filter_eq ha, mul_sum]
  push_cast
  constructor
  · have h : ∑ k ∈ range (N + 1), (t * μ k - T) ≤ ∑ k ∈ range (N + 1), (#{r | a r = k} : ℝ) := by
      apply sum_le_sum
      intro k hk
      obtain ⟨h, -⟩ := hD k hk
      exact h
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at h
    push_cast at h
    linarith
  · apply sum_le_sum
    intro k hk
    obtain ⟨-, h⟩ := hD k hk
    exact h

lemma sum_card_filter_mul_log_inv_geomDist {a : Fin n → ℕ} (ha : ∀ r, a r ≤ N) (hρ : 0 < ρ) :
    ∑ k ∈ range (N + 1), #{r | a r = k} * log (geomDist N ρ k)⁻¹ =
      n * log (∑ k ∈ range (N + 1), ρ ^ k) -
        (∑ k ∈ range (N + 1), (k : ℝ) * #{r | a r = k}) * log ρ := by
  simp only [log_inv_geomDist hρ, mul_sub, sum_sub_distrib, ← sum_mul,
    (by exact_mod_cast sum_card_filter_eq ha : ∑ k ∈ range (N + 1), (#{r | a r = k} : ℝ) = n)]
  congr 1
  rw [sum_mul]
  congr with k
  ring

/-- **The empirical mean.** If `geomDist N ρ` has mean `N / 3`, each value `k ≤ N` appears in `a`
at least `t * geomDist N ρ k - T` times and `n ≤ t`, then the entries of `a` sum to at least
`n * N / 3 - T * N * (N + 1)`. -/
lemma mul_div_sub_le_sum_mul_card_filter {a : Fin n → ℕ} (hρ : 0 < ρ)
    (hmean : 3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k) {t T : ℝ}
    (hT : 0 ≤ T) (hD : ∀ k ∈ range (N + 1), t * geomDist N ρ k - T ≤ #{r | a r = k})
    (hnt : n ≤ t) :
    n * N / 3 - T * N * (N + 1) ≤ ∑ k ∈ range (N + 1), (k : ℝ) * #{r | a r = k} := by
  have h₁ : ∑ k ∈ range (N + 1), (k : ℝ) * (t * geomDist N ρ k - T) ≤
      ∑ k ∈ range (N + 1), (k : ℝ) * #{r | a r = k} := by
    gcongr with k hk
    exact hD k hk
  have h₂ : ∑ k ∈ range (N + 1), (k : ℝ) ≤ N * (N + 1) := by
    grw [sum_le_card_nsmul (range (N + 1)) (fun k : ℕ ↦ (k : ℝ)) N (by simp)]
    simp [mul_comm]
  simp only [mul_sub, sum_sub_distrib, mul_left_comm _ t, ← mul_sum, ← sum_mul,
    sum_mul_geomDist hρ hmean] at h₁
  linarith [mul_le_mul_of_nonneg_right h₂ hT, mul_le_mul_of_nonneg_right hnt N.cast_nonneg]

/-- If `D ∈ [t * ψ - T, t * ψ]` and `n ∈ [t - S, t]` with `0 ≤ T ≤ S`, `1 ≤ n` and
`0 < y ≤ ψ ≤ 1`, then `(D - n * ψ) ^ 2 / (n * ψ) ≤ S ^ 2 / y`. -/
lemma sq_sub_mul_div_mul_le {D n t S T ψ y : ℝ} (hy : 0 < y) (hyψ : y ≤ ψ) (hψ : ψ ≤ 1)
    (hn : 1 ≤ n) (hT : 0 ≤ T) (hTS : T ≤ S) (hD : D ∈ Set.Icc (t * ψ - T) (t * ψ))
    (hnt : n ∈ Set.Icc (t - S) t) :
    (D - n * ψ) ^ 2 / (n * ψ) ≤ S ^ 2 / y := by
  obtain ⟨hD₁, hD₂⟩ := hD
  obtain ⟨hn₁, hn₂⟩ := hnt
  gcongr ?_ / ?_
  · exact sq_le_sq' (by nlinarith) (by nlinarith)
  · nlinarith

/-- **Type classes near the geometric distribution.** If `ρ ∈ (0, 1)`, `geomDist N ρ` has mean
`N / 3` and each value `k ≤ N` appears in `a` between `t * geomDist N ρ k - T` and
`t * geomDist N ρ k` times, then `log #(typeClass a)` is at least
`n * (log (∑ k, ρ ^ k) - N / 3 * log ρ)` minus an error of order `log n`. -/
lemma le_log_card_typeClass_geomDist (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (hmean : 3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k) {T t : ℝ}
    (hT : 0 ≤ T) (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) (hn : 1 ≤ n)
    (hD : ∀ k ∈ range (N + 1),
      (#{r | a r = k} : ℝ) ∈ Set.Icc (t * geomDist N ρ k - T) (t * geomDist N ρ k)) :
    n * (log (∑ k ∈ range (N + 1), ρ ^ k) - N / 3 * log ρ) -
        ((N + 1) * (1 + ((N + 1) * T) ^ 2 / geomDist N ρ N) - T * N * (N + 1) * log ρ) -
        (N + 1) * log (n + 1) ≤ log #(typeClass a) := by
  have hnt := natCast_mem_Icc_of_card_filter_mem_Icc ha hD
  rw [sum_geomDist hρ₀, mul_one] at hnt
  have hquad (k : ℕ) (hk : k ∈ range (N + 1)) :
      (#{r | a r = k} - n * geomDist N ρ k) ^ 2 / (n * geomDist N ρ k) ≤
        ((N + 1) * T) ^ 2 / geomDist N ρ N :=
    sq_sub_mul_div_mul_le (geomDist_pos hρ₀ N)
      (geomDist_le_geomDist hρ₀ hρ₁ (mem_range_succ_iff.1 hk))
      (geomDist_le_one hρ₀ (mem_range_succ_iff.1 hk)) (by exact_mod_cast hn) hT
      (le_mul_of_one_le_left hT (by simp)) (hD k hk) hnt
  have key := le_log_card_typeClass a ha (fun k _ ↦ geomDist_pos hρ₀ k) (sum_geomDist hρ₀)
  rw [sum_card_filter_mul_log_inv_geomDist ha hρ₀] at key
  grw [sum_le_sum hquad] at key
  obtain ⟨-, hnt⟩ := hnt
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add_one] at key
  nlinarith [mul_le_mul_of_nonpos_right (mul_div_sub_le_sum_mul_card_filter hρ₀ hmean hT
    (fun k hk ↦ (hD k hk).1) hnt) (log_neg hρ₀ hρ₁).le]

/-- `(1 - c (N + 1)) * log (N + 1) ≤ log (∑ k, ρ ^ k) - N / 3 * log ρ` for `ρ ∈ (0, 1)`, by the
definition of `c`. -/
lemma one_sub_c_mul_log_le (hN : 0 < N) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    (1 - c (N + 1)) * log (N + 1) ≤ log (∑ k ∈ range (N + 1), ρ ^ k) - N / 3 * log ρ := by
  have h := log_le_log (by positivity) (rpow_one_sub_c_le (p := N + 1) (by grind) hρ₀ hρ₁)
  rw [log_rpow (by positivity),
    log_mul (by positivity) (geom_sum_pos hρ₀.le (by simp : N + 1 ≠ 0)).ne', log_rpow hρ₀] at h
  push_cast at h
  linarith

/-- Listing every `x ∈ s` exactly `C x` times gives a sequence `f` with values in `s` taking the
value `k` under `g` exactly `∑ x ∈ s with g x = k, C x` times. -/
lemma exists_card_filter_eq_sum {α β : Type*} [DecidableEq β] (s : Finset α) (C : α → ℕ) :
    ∃ (n : ℕ) (f : Fin n → α), (∀ r, f r ∈ s) ∧
      ∀ (g : α → β) (k : β), #{r | g (f r) = k} = ∑ x ∈ s with g x = k, C x := by
  classical
  let e := Fintype.equivFin (Σ x : s, Fin (C x))
  refine ⟨_, fun r ↦ (e.symm r).fst, fun r ↦ (e.symm r).fst.prop, ?_⟩
  intro g k
  rw [card_equiv e.symm (t := {x | g x.fst = k}) (by simp), card_filter, Fintype.sum_sigma,
    sum_filter, ← sum_coe_sort s]
  simp [apply_ite card]

/-- **Rounding a coupling.** Rounding `t * J` down on the triples with sum `N` gives a sequence
`f₀` of such triples in which, for every `g`, the value `k` of `g` appears between
`t * marginal N J g k - #(sumTriples N)` and `t * marginal N J g k` times. -/
lemma exists_card_filter_mem_Icc {J : ℕ × ℕ × ℕ → ℝ} (hJ : ∀ x, 0 ≤ J x) {t : ℝ} (ht : 0 ≤ t) :
    ∃ (n : ℕ) (f₀ : Fin n → ℕ × ℕ × ℕ), (∀ r, f₀ r ∈ sumTriples N) ∧
      ∀ (g : ℕ × ℕ × ℕ → ℕ) (k : ℕ), (#{r | g (f₀ r) = k} : ℝ) ∈
        Set.Icc (t * marginal N J g k - #(sumTriples N)) (t * marginal N J g k) := by
  obtain ⟨n, f₀, hf₀, hcard⟩ :=
    exists_card_filter_eq_sum (β := ℕ) (sumTriples N) fun x ↦ ⌊t * J x⌋₊
  refine ⟨n, f₀, hf₀, ?_⟩
  intro g k
  rw [hcard, marginal, mul_sum]
  push_cast
  constructor
  · have h : ∑ x ∈ sumTriples N with g x = k, (t * J x - 1) ≤
        ∑ x ∈ sumTriples N with g x = k, (⌊t * J x⌋₊ : ℝ) := by
      apply sum_le_sum
      intro x _
      exact (Nat.sub_one_lt_floor _).le
    rw [sum_sub_distrib, sum_const, nsmul_one] at h
    linarith [(Nat.cast_le (α := ℝ)).2 (card_filter_le (sumTriples N) fun x ↦ g x = k)]
  · apply sum_le_sum
    intro x _
    exact Nat.floor_le (mul_nonneg ht (hJ x))

lemma marginal_inv_smul_eq_geomDist {J : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ}
    (hg : marginal N J g = geom N ρ) {k : ℕ} (hk : k ≤ N) :
    marginal N ((∑ j ∈ range (N + 1), ρ ^ j)⁻¹ • J) g k = geomDist N ρ k := by
  simp [marginal_smul, hg, geom, geomDist, hk, div_eq_inv_mul]

/-- **Base points with large type classes.** For `p ≥ 2` and `d ≥ p ^ 4 + 1` there are
`n ∈ [d - p ^ 4, d]` and `a₀ b₀ c₀ : Fin n → ℕ` with `a₀ r + b₀ r + c₀ r = p - 1` whose type
classes all have at least `exp (n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1))`
elements. -/
lemma exists_le_log_card_typeClass {p d : ℕ} (hp : 2 ≤ p) (hd : p ^ 4 + 1 ≤ d) :
    ∃ (n : ℕ) (a₀ b₀ c₀ : Fin n → ℕ),
      (∀ r, a₀ r + b₀ r + c₀ r = p - 1) ∧ d - (p : ℝ) ^ 4 ≤ n ∧ n ≤ d ∧
      n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1) ≤ log #(typeClass a₀) ∧
      n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1) ≤ log #(typeClass b₀) ∧
      n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1) ≤ log #(typeClass c₀) := by
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := ⟨p - 1, by grind⟩
  obtain ⟨ρ, hρ, hρ₁, hmean, J, hJ, h₁, h₂, h₃⟩ := exists_compatible_geom (N := N) (by grind)
  have hρ₀ : 0 < ρ := by linarith
  have hS : (#(sumTriples N) : ℝ) ≤ (N + 1) ^ 3 := by
    have hsub : sumTriples N ⊆ range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1) := by
      rintro ⟨a, b, c⟩ h
      simp only [mem_sumTriples] at h
      simp only [mem_product, mem_range]
      grind
    have : #(sumTriples N) ≤ (N + 1) ^ 3 := by
      grw [card_le_card hsub]
      simp [card_product, pow_three]
    exact_mod_cast this
  have hK : (N + 1) * (1 + ((N + 1) * #(sumTriples N)) ^ 2 / geomDist N ρ N) -
      #(sumTriples N) * N * (N + 1) * log ρ ≤ 2 ^ (N + 1) * (N + 1) ^ 10 := by
    have hg : (geomDist N ρ N)⁻¹ ≤ (N + 1) * 2 ^ N := by
      rw [geomDist, inv_div, div_le_iff₀ (by positivity)]
      have : ∑ j ∈ range (N + 1), ρ ^ j ≤ N + 1 := by
        grw [sum_le_card_nsmul _ _ 1 fun j _ ↦ pow_le_one₀ hρ₀.le hρ₁.le]
        simp
      nlinarith [(by rw [← mul_pow]; exact one_le_pow₀ (by linarith) : 1 ≤ 2 ^ N * ρ ^ N)]
    have hlog : -log ρ ≤ 1 := by
      have := log_le_log (by norm_num) hρ
      rw [one_div, log_inv] at this
      linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hq : (2 : ℝ) ≤ N + 1 := by exact_mod_cast hp
    have hq₅ : (2 : ℝ) ≤ (N + 1) ^ 5 := hq.trans (le_self_pow₀ (by linarith) (by norm_num))
    have hsq : ((N + 1) * #(sumTriples N) : ℝ) ^ 2 / geomDist N ρ N ≤
        ((N + 1) * (N + 1) ^ 3) ^ 2 * ((N + 1) * 2 ^ N) := by
      rw [div_eq_mul_inv]
      gcongr
      exact (inv_pos.2 (geomDist_pos hρ₀ N)).le
    have hlin : #(sumTriples N) * N * (N + 1) * -log ρ ≤ (N + 1) ^ 3 * (N + 1) * (N + 1) * 1 := by
      gcongr
      · linarith [log_neg hρ₀ hρ₁]
      · linarith
    have hq₁₀ : (N + 1 : ℝ) + (N + 1) ^ 5 ≤ 2 ^ N * (N + 1) ^ 10 := by
      have : (N + 1 : ℝ) ≤ (N + 1) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
      have : 2 * (N + 1 : ℝ) ^ 5 ≤ (N + 1) ^ 10 := by
        nlinarith [(by ring : (N + 1 : ℝ) ^ 10 = (N + 1) ^ 5 * (N + 1) ^ 5)]
      nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := N),
        (by positivity : (0 : ℝ) ≤ (N + 1) ^ 10)]
    rw [pow_succ (2 : ℝ) N]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ N + 1)]
  have hT : (N + 1) * (#(sumTriples N) : ℝ) ≤ (N + 1) ^ 4 := by
    grw [hS]
    exact le_of_eq (by ring)
  have hd' : ((N + 1) ^ 4 + 1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨n, f₀, hf₀, hcount⟩ := exists_card_filter_mem_Icc (N := N)
    (J := (∑ j ∈ range (N + 1), ρ ^ j)⁻¹ • J)
    (fun x ↦ mul_nonneg (inv_pos.2 (geom_sum_pos hρ₀.le N.succ_ne_zero)).le (hJ x))
    d.cast_nonneg
  have hD (g : ℕ × ℕ × ℕ → ℕ) (hg : marginal N J g = geom N ρ) (k : ℕ)
      (hk : k ∈ range (N + 1)) : (#{r | g (f₀ r) = k} : ℝ) ∈
        Set.Icc (d * geomDist N ρ k - #(sumTriples N)) (d * geomDist N ρ k) := by
    rw [← marginal_inv_smul_eq_geomDist hg (mem_range_succ_iff.1 hk)]
    exact hcount g k
  obtain ⟨a₀, b₀, c₀, rfl⟩ : ∃ a₀ b₀ c₀ : Fin n → ℕ, f₀ = fun r ↦ (a₀ r, b₀ r, c₀ r) :=
    ⟨_, _, _, rfl⟩
  have hsum (r : Fin n) : a₀ r + b₀ r + c₀ r = N := mem_sumTriples.1 (hf₀ r)
  obtain ⟨hn₁, hn₂⟩ := natCast_mem_Icc_of_card_filter_mem_Icc (fun r ↦ by grind [hsum r])
    (hD _ h₁)
  rw [sum_geomDist hρ₀, mul_one] at hn₁ hn₂
  have hlog (g : ℕ × ℕ × ℕ → ℕ) (hga : ∀ r, g (a₀ r, b₀ r, c₀ r) ≤ N)
      (hg : marginal N J g = geom N ρ) :
      n * ((1 - c (N + 1)) * log (N + 1 : ℕ)) - 2 ^ (N + 1) * (N + 1 : ℕ) ^ 10 -
        (N + 1 : ℕ) * log (n + 1) ≤ log #(typeClass fun r ↦ g (a₀ r, b₀ r, c₀ r)) := by
    push_cast
    nlinarith [le_log_card_typeClass_geomDist hρ₀ hρ₁ hmean (Nat.cast_nonneg _) _ hga
      (by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)) (hD g hg),
      mul_le_mul_of_nonneg_left (one_sub_c_mul_log_le (N := N) (by grind) hρ₀ hρ₁) n.cast_nonneg]
  exact ⟨n, a₀, b₀, c₀, fun r ↦ by grind [hsum r], by push_cast; linarith,
    by exact_mod_cast hn₂, hlog (fun (a, _, _) ↦ a) (fun r ↦ by grind [hsum r]) h₁,
    hlog (fun (_, b, _) ↦ b) (fun r ↦ by grind [hsum r]) h₂,
    hlog (fun (_, _, c) ↦ c) (fun r ↦ by grind [hsum r]) h₃⟩

/-- Extending the vectors of a multicolored sum-free family by zero coordinates keeps it
multicolored sum-free. -/
lemma IsMulticoloredSumFree.extend {ι G : Type*} [AddCommGroup G] {x y z : ι → Fin n → G}
    (h : IsMulticoloredSumFree x y z) {d : ℕ} (hnd : n ≤ d) :
    IsMulticoloredSumFree (fun i ↦ Function.extend (Fin.castLE hnd) (x i) 0)
      (fun i ↦ Function.extend (Fin.castLE hnd) (y i) 0)
      fun i ↦ Function.extend (Fin.castLE hnd) (z i) 0 :=
  h.map (Function.ExtendByZero.hom G (Fin.castLE hnd))
    (Function.extend_injective (Fin.castLE_injective hnd) 0)

/-- **A family in every large dimension.** For `p ≥ 2` and `d ≥ p ^ 4 + 1` there are
`n ∈ [d - p ^ 4, d]` and a multicolored sum-free family in `Fin d → ZMod p` with at least
`exp (n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1) -
4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) / (4 * (12 + 2 * p))` members. -/
lemma exists_isMulticoloredSumFree_exp_le {p d : ℕ} (hp : 2 ≤ p) (hd : p ^ 4 + 1 ≤ d) :
    ∃ (n m : ℕ) (x y z : Fin m → Fin d → ZMod p),
      IsMulticoloredSumFree x y z ∧ d - (p : ℝ) ^ 4 ≤ n ∧ n ≤ d ∧
        exp (n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1) -
          4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) / (4 * (12 + 2 * p)) ≤ m := by
  obtain ⟨n, a₀, b₀, c₀, h₀, hn₁, hn₂, ha, hb, hc⟩ := exists_le_log_card_typeClass hp hd
  have hw (a : Fin n → ℕ) (h : n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1) ≤
      log #(typeClass a)) :
      max 1 (exp (n * ((1 - c p) * log p) - 2 ^ p * p ^ 10 - p * log (n + 1))) ≤
        #(typeClass a) :=
    max_le (Nat.one_le_cast.2 (typeClass_nonempty a).card_pos)
      ((le_log_iff_exp_le (Nat.cast_pos.2 (typeClass_nonempty a).card_pos)).1 h)
  obtain ⟨m, x, y, z, hsf, hm⟩ := exists_isMulticoloredSumFree_of_typeClass hp h₀
    (le_max_left _ _) (hw _ ha) (hw _ hb) (hw _ hc)
  have hnd : n ≤ d := by exact_mod_cast hn₂
  refine ⟨n, m, _, _, _, hsf.extend hnd, hn₁, hn₂, ?_⟩
  grw [← hm]
  rw [div_le_div_iff_of_pos_right (by positivity), sub_eq_add_neg _ (4 * √_), exp_add, ← neg_mul]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le

/-- For `a > 0`, `b * √(d + 1) ≤ a * d` once `(2 * b / a) ^ 2 + 1 ≤ d`. -/
lemma mul_sqrt_add_one_le {a b : ℝ} (ha : 0 < a) {d : ℕ} (hd : (2 * b / a) ^ 2 + 1 ≤ d) :
    b * √(d + 1) ≤ a * d := by
  have hb : 2 * b / a ≤ √(d + 1) := (le_abs_self _).trans (abs_le_sqrt (by linarith))
  rw [div_le_iff₀ ha] at hb
  nlinarith [sq_sqrt (by positivity : (0 : ℝ) ≤ d + 1), sqrt_nonneg (d + 1)]

/-- The error terms of `exists_isMulticoloredSumFree_exp_le` are at most `ε * d` for large `d`:
for every `A` and `ε > 0`, `A + p * log (n + 1) + 4 * √(log ((12 + 2 * p) * p ^ (3 * n))) ≤ ε * d`
for every `n ≤ d` once `(2 * b / ε) ^ 2 + 1 ≤ d`, where
`b = |A| + 2 * p + 4 * √(log (12 + 2 * p) + 3 * log p)`. -/
lemma add_mul_log_add_sqrt_le {p : ℕ} (hp : 2 ≤ p) {A ε : ℝ} (hε : 0 < ε) {d : ℕ}
    (hd : (2 * (|A| + 2 * p + 4 * √(log (12 + 2 * p) + 3 * log p)) / ε) ^ 2 + 1 ≤ d) {n : ℕ}
    (hn : n ≤ d) : A + p * log (n + 1) + 4 * √(log ((12 + 2 * p) * p ^ (3 * n))) ≤ ε * d := by
  have hn' : (n : ℝ) ≤ d := by exact_mod_cast hn
  have hlog : log (n + 1) ≤ 2 * √(d + 1) := by
    grw [log_le_log (by positivity) (by linarith : (n : ℝ) + 1 ≤ d + 1),
      log_le_rpow_div (by positivity) (by norm_num : (0 : ℝ) < 1 / 2), ← sqrt_eq_rpow]
    linarith
  have hsq : √(log ((12 + 2 * p) * p ^ (3 * n))) ≤
      √(log (12 + 2 * p) + 3 * log p) * √(d + 1) := by
    rw [← sqrt_mul' _ (by positivity)]
    apply sqrt_le_sqrt
    rw [log_mul (by positivity) (by positivity), log_pow]
    push_cast
    nlinarith [log_nonneg (by linarith [p.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ 12 + 2 * p),
      log_nonneg (by exact_mod_cast (by grind : 1 ≤ p) : (1 : ℝ) ≤ p)]
  nlinarith [mul_sqrt_add_one_le hε hd, (le_abs_self A).trans (le_mul_of_one_le_right
    (abs_nonneg A) (one_le_sqrt.2 (by simp) : (1 : ℝ) ≤ √(d + 1))), p.cast_nonneg (α := ℝ)]

/-- The constant `b` of `add_mul_log_add_sqrt_le` for the error terms of
`exists_isMulticoloredSumFree_exp_le` is at most `2 ^ (p + 1) * p ^ 10`. -/
lemma abs_add_mul_add_sqrt_le {p : ℕ} (hp : 2 ≤ p) :
    |(1 - c p) * log p * p ^ 4 + 2 ^ p * p ^ 10 + log (4 * (12 + 2 * p))| + 2 * p +
      4 * √(log (12 + 2 * p) + 3 * log p) ≤ 2 ^ (p + 1) * p ^ 10 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hc₀ := c_pos hp
  have hc₁ := c_lt_one hp
  have hlogp : log p ≤ p := log_le_self (by positivity)
  have hlogp₀ : 0 ≤ log p := log_nonneg (by linarith)
  have hlog₁ : log (4 * (12 + 2 * p)) ≤ 4 * (12 + 2 * p) := log_le_self (by positivity)
  have hlog₂ : log (12 + 2 * p) ≤ 12 + 2 * p := log_le_self (by positivity)
  have hlog₂₀ : 0 ≤ log (12 + 2 * p) := log_nonneg (by linarith)
  have hsqrt : √(log (12 + 2 * p) + 3 * log p) ≤ 13 + 5 * p := by
    rw [sqrt_le_left (by linarith)]
    nlinarith
  have h₄ : (16 : ℝ) * p ≤ p ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hp' 4
    norm_num at this
    nlinarith
  have h₅ : (32 : ℝ) ≤ p ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hp' 5
    norm_num at this
    exact this
  have h₁ : (1 - c p) * log p * p ^ 4 ≤ p ^ 5 := by
    have : (1 - c p) * log p ≤ p := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ p ^ 4)]
  have h₁₀ : 0 ≤ (1 - c p) * log p * p ^ 4 := by
    have : 0 ≤ 1 - c p := by linarith
    positivity
  have h₂ : (32 : ℝ) * p ^ 5 ≤ 2 ^ p * p ^ 10 := by
    calc (32 : ℝ) * p ^ 5 ≤ (p : ℝ) ^ 5 * p ^ 5 := by gcongr
      _ = (p : ℝ) ^ 10 := by ring
      _ ≤ 2 ^ p * p ^ 10 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  rw [abs_of_nonneg (by linarith [log_nonneg (by linarith : (1 : ℝ) ≤ 4 * (12 + 2 * p)),
    (by positivity : (0 : ℝ) ≤ 2 ^ p * p ^ 10)]), pow_succ (2 : ℝ) p]
  linarith

/-- **Large multicolored sum-free families** (Kleinberg, Sawin and Speyer, using Pebody's theorem;
the second part of Theorem 2 of Fox and Lovász). For `p ≥ 2`, `η > 0` and
`n ≥ sumFreeDim p η = ⌈(2 ^ (p + 3) * p ^ 10 / η) ^ 2⌉ + p ^ 4 + 1`, there is a multicolored
sum-free family in `Fin n → ZMod p` with at least `p ^ ((1 - c p - η) * n)` members. -/
theorem exists_isMulticoloredSumFree_rpow_le {p d : ℕ} (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η)
    (hd : sumFreeDim p η ≤ d) :
    ∃ (m : ℕ) (x y z : Fin m → Fin d → ZMod p),
      IsMulticoloredSumFree x y z ∧ (p : ℝ) ^ ((1 - c p - η) * d) ≤ m := by
  unfold sumFreeDim at hd
  have hlogp : 1 / 2 ≤ log p := by
    linarith [one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2),
      log_le_log (by norm_num) (by exact_mod_cast hp : (2 : ℝ) ≤ p)]
  have hb : (2 * (|(1 - c p) * log p * p ^ 4 + 2 ^ p * p ^ 10 + log (4 * (12 + 2 * p))| +
      2 * p + 4 * √(log (12 + 2 * p) + 3 * log p)) / (η * log p)) ^ 2 + 1 ≤ d := by
    have h := abs_add_mul_add_sqrt_le hp
    have hd' : ((⌈(2 ^ (p + 3) * (p : ℝ) ^ 10 / η) ^ 2⌉₊ + p ^ 4 + 1 : ℕ) : ℝ) ≤ d := by
      exact_mod_cast hd
    push_cast at hd'
    have hle : 2 * (|(1 - c p) * log p * p ^ 4 + 2 ^ p * p ^ 10 + log (4 * (12 + 2 * p))| +
        2 * p + 4 * √(log (12 + 2 * p) + 3 * log p)) / (η * log p) ≤
          2 ^ (p + 3) * p ^ 10 / η := by
      rw [div_le_div_iff₀ (by positivity) hη, pow_add]
      grw [h, pow_succ]
      nlinarith [(by positivity : (0 : ℝ) ≤ 2 ^ p * p ^ 10 * η)]
    grw [hle]
    linarith [Nat.le_ceil ((2 ^ (p + 3) * (p : ℝ) ^ 10 / η) ^ 2),
      (by positivity : (0 : ℝ) ≤ p ^ 4)]
  obtain ⟨n, m, x, y, z, hsf, hn₁, hn₂, hm⟩ := exists_isMulticoloredSumFree_exp_le hp (d := d)
    (by grind)
  refine ⟨m, x, y, z, hsf, ?_⟩
  grw [← hm]
  rw [rpow_def_of_pos (by positivity), le_div_iff₀ (by positivity),
    ← exp_log (by positivity : (0 : ℝ) < 4 * (12 + 2 * p)), ← exp_add, exp_le_exp]
  nlinarith [add_mul_log_add_sqrt_le hp (mul_pos hη (by linarith)) hb
      (by exact_mod_cast hn₂ : n ≤ d),
    mul_le_mul_of_nonneg_right hn₁
      (mul_nonneg (sub_nonneg.2 (c_lt_one hp).le) (by linarith : (0 : ℝ) ≤ log p))]

end ArithmeticTriangleRemovalInVectorSpaces
