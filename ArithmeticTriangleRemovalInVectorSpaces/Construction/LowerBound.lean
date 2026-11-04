/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.Construction.TypeClass
public import ArithmeticTriangleRemovalInVectorSpaces.Coupling.Basic
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
import ArithmeticTriangleRemovalInVectorSpaces.Construction.Family
import ArithmeticTriangleRemovalInVectorSpaces.Coupling.Pebody
import Mathlib.Algebra.BigOperators.Field

/-!
# Large multicolored sum-free families

Kleinberg, Sawin and Speyer showed that the exponent `1 - c p` in the bound on multicolored
sum-free families in `Fin n → ZMod p` cannot be lowered. Pebody's theorem gives a coupling `J` of
three copies of the truncated geometric distribution `k ↦ ρ ^ k` on `[0, p - 1]` with mean
`(p - 1) / 3`. Rounding `t J` down gives a base point whose coordinates have the empirical
distributions `t ρ ^ k` up to a bounded error, so their type classes have about
`(ρ ^ (-(p - 1) / 3) ∑ k, ρ ^ k) ^ n ≥ p ^ ((1 - c p) n)` elements. The sum-free family of this
base point, padded with zero coordinates, has at least `p ^ ((1 - c p - η) n)` members for large
`n`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_base`: rounding a coupling to a base point.
* `ArithmeticTriangleRemovalInVectorSpaces.le_log_card_typeClass_geom`: the size of a type class
  whose empirical distribution is close to a multiple of `k ↦ ρ ^ k`.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_exp_le`: a family in every
  large dimension, with a lower bound on its size.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_forall_ge_exists_isMulticoloredSumFree`: for
  every `η > 0` and large `n`, there is a multicolored sum-free family in `Fin n → ZMod p` with at
  least `p ^ ((1 - c p - η) n)` members (the second part of Theorem 2 of Fox and Lovász).
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n N : ℕ}

lemma sum_card_filter_eq {a : Fin n → ℕ} (ha : ∀ r, a r ≤ N) :
    ∑ k ∈ range (N + 1), #{r | a r = k} = n := by
  rw [← card_eq_sum_card_fiberwise (fun r _ ↦ mem_range.2 (by grind [ha r])), card_univ,
    Fintype.card_fin]

/-- If the value `k` appears in `a` between `t π k - T` and `t π k` times, then `n` lies between
`t ∑ k, μ k - (N + 1) T` and `t ∑ k, μ k`. -/
lemma card_bounds {a : Fin n → ℕ} (ha : ∀ r, a r ≤ N) {μ : ℕ → ℝ} {t T : ℝ}
    (hD : ∀ k ∈ range (N + 1), t * μ k - T ≤ #{r | a r = k} ∧ (#{r | a r = k} : ℝ) ≤ t * μ k) :
    t * ∑ k ∈ range (N + 1), μ k - (N + 1) * T ≤ n ∧ (n : ℝ) ≤ t * ∑ k ∈ range (N + 1), μ k := by
  have h := congrArg (Nat.cast (R := ℝ)) (sum_card_filter_eq ha)
  push_cast at h
  rw [← h, mul_sum]
  refine ⟨?_, ?_⟩
  · have h₁ : ∑ k ∈ range (N + 1), (t * μ k - T) ≤ ∑ k ∈ range (N + 1), (#{r | a r = k} : ℝ) := by
      apply sum_le_sum
      intro k hk
      exact (hD k hk).1
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at h₁
    push_cast at h₁
    linarith
  · apply sum_le_sum
    intro k hk
    exact (hD k hk).2

/-- One term of the quadratic error in `le_log_card_typeClass`, for `ψ = x / G`. -/
lemma sq_sub_div_le {D n t T S G x y : ℝ} (hx : y ≤ x) (hy : 0 < y) (hxG : x ≤ G) (hn : 1 ≤ n)
    (hTS : T ≤ S) (hT : 0 ≤ T) (hD₁ : t * x - T ≤ D) (hD₂ : D ≤ t * x) (hn₁ : t * G - S ≤ n)
    (hn₂ : n ≤ t * G) :
    (D - n * (x / G)) ^ 2 / (n * (x / G)) ≤ S ^ 2 * G / y := by
  have hG : 0 < G := hy.trans_le (hx.trans hxG)
  have hxG₀ : 0 ≤ x / G := div_nonneg (hy.le.trans hx) hG.le
  have he : t * G * (x / G) = t * x := by field_simp
  have h₁ : t * x - S * (x / G) ≤ n * (x / G) := by
    rw [← he, ← sub_mul]
    gcongr
  have h₂ : n * (x / G) ≤ t * x := by
    rw [← he]
    gcongr
  have hS : S * (x / G) ≤ S := mul_le_of_le_one_right (hT.trans hTS) ((div_le_one hG).2 hxG)
  calc (D - n * (x / G)) ^ 2 / (n * (x / G)) ≤ S ^ 2 / (y / G) := by
        apply div_le_div₀ (sq_nonneg S) (sq_le_sq' (by linarith) (by linarith)) (by positivity)
        grw [div_le_div_of_nonneg_right hx hG.le]
        exact le_mul_of_one_le_left hxG₀ hn
    _ = S ^ 2 * G / y := by field_simp

/-- **Type classes near the geometric distribution.** If `ρ ∈ (0, 1)` has mean `N / 3` on
`[0, N]` and the value `k` appears in `a` between `t ρ ^ k - T` and `t ρ ^ k` times, then the
logarithm of the type class of `a` is at least `n log (ρ ^ (-N / 3) ∑ k, ρ ^ k)` up to an error
of order `log n`. -/
lemma le_log_card_typeClass_geom {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (hmean : 3 * ∑ k ∈ range (N + 1), k * ρ ^ k = N * ∑ k ∈ range (N + 1), ρ ^ k) {T t : ℝ}
    (hT : 0 ≤ T) (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) (hn : 1 ≤ n)
    (hD : ∀ k ∈ range (N + 1), t * ρ ^ k - T ≤ #{r | a r = k} ∧ (#{r | a r = k} : ℝ) ≤ t * ρ ^ k) :
    n * (log (∑ k ∈ range (N + 1), ρ ^ k) - N / 3 * log ρ) -
        ((N + 1) * (1 + ((N + 1) * T) ^ 2 * (∑ k ∈ range (N + 1), ρ ^ k) / ρ ^ N) -
          T * N * (N + 1) * log ρ) - (N + 1) * log (n + 1) ≤ log #(typeClass a) := by
  set G := ∑ k ∈ range (N + 1), ρ ^ k
  have hρk (k : ℕ) (hk : k ∈ range (N + 1)) : ρ ^ k ≤ G :=
    single_le_sum (fun j _ ↦ (pow_pos hρ₀ j).le) hk
  have hG : 0 < G := (pow_pos hρ₀ 0).trans_le (hρk 0 (by simp))
  obtain ⟨hn₁, hn₂⟩ := card_bounds ha hD
  have hnsum := congrArg (Nat.cast (R := ℝ)) (sum_card_filter_eq ha)
  push_cast at hnsum
  have key := le_log_card_typeClass a ha (ψ := fun k ↦ ρ ^ k / G) (fun k _ ↦ by positivity)
    (by rw [← sum_div, div_self hG.ne'])
  have hmain : ∑ k ∈ range (N + 1), (#{r | a r = k} : ℝ) * log (ρ ^ k / G)⁻¹ =
      (∑ k ∈ range (N + 1), (#{r | a r = k} : ℝ)) * log G -
        (∑ k ∈ range (N + 1), k * (#{r | a r = k} : ℝ)) * log ρ := by
    rw [sum_mul, sum_mul, ← sum_sub_distrib]
    congr with k
    rw [inv_div, log_div hG.ne' (pow_pos hρ₀ k).ne', log_pow]
    ring
  have hmom : n * N / 3 - T * N * (N + 1) ≤ ∑ k ∈ range (N + 1), k * (#{r | a r = k} : ℝ) := by
    have h₁ : ∑ k ∈ range (N + 1), k * (t * ρ ^ k - T) ≤
        ∑ k ∈ range (N + 1), k * (#{r | a r = k} : ℝ) := by
      apply sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hD k hk).1 k.cast_nonneg
    have h₂ : ∑ k ∈ range (N + 1), (k : ℝ) ≤ N * (N + 1) := by
      grw [sum_le_sum (g := fun _ ↦ (N : ℝ)) fun k hk ↦ Nat.cast_le.2 (mem_range_succ_iff.1 hk)]
      simp [mul_comm]
    simp only [mul_sub, sum_sub_distrib, mul_left_comm _ t, ← mul_sum, ← sum_mul] at h₁
    have h₃ : t * (3 * ∑ k ∈ range (N + 1), k * ρ ^ k) = t * (N * G) := by rw [hmean]
    linarith [mul_le_mul_of_nonneg_left hn₂ N.cast_nonneg, mul_le_mul_of_nonneg_right h₂ hT]
  have hquad : ∑ k ∈ range (N + 1), ((#{r | a r = k} : ℝ) - n * (ρ ^ k / G)) ^ 2 /
      (n * (ρ ^ k / G)) ≤ (N + 1) * (((N + 1) * T) ^ 2 * G / ρ ^ N) := by
    have h (k : ℕ) (hk : k ∈ range (N + 1)) : ((#{r | a r = k} : ℝ) - n * (ρ ^ k / G)) ^ 2 /
        (n * (ρ ^ k / G)) ≤ ((N + 1) * T) ^ 2 * G / ρ ^ N := by
      obtain ⟨hD₁, hD₂⟩ := hD k hk
      exact sq_sub_div_le (pow_le_pow_of_le_one hρ₀.le hρ₁.le (by grind))
        (pow_pos hρ₀ N) (hρk k hk) (by exact_mod_cast hn) (le_mul_of_one_le_left hT (by simp))
        hT hD₁ hD₂ hn₁ hn₂
    grw [sum_le_sum h]
    simp
  rw [hmain, hnsum] at key
  linarith [mul_le_mul_of_nonpos_right hmom (log_neg hρ₀ hρ₁).le]

/-- **Rounding a coupling.** Rounding `t J` down on the triples with sum `N` gives a base point
`f₀` in which, for every `g`, the value `k` of `g` appears between `t m_k - |T|` and `t m_k`
times, where `m` is the marginal of `J` along `g` and `T` is the set of triples. -/
lemma exists_base {J : ℕ × ℕ × ℕ → ℝ} (hJ : ∀ x, 0 ≤ J x) {t : ℝ} (ht : 0 ≤ t) :
    ∃ (n : ℕ) (f₀ : Fin n → ℕ × ℕ × ℕ), (∀ r, f₀ r ∈ sumTriples N) ∧
      ∀ (g : ℕ × ℕ × ℕ → ℕ) (k : ℕ),
        t * marginal N J g k - #(sumTriples N) ≤ #{r | g (f₀ r) = k} ∧
          (#{r | g (f₀ r) = k} : ℝ) ≤ t * marginal N J g k := by
  set C : ℕ × ℕ × ℕ → ℕ := fun x ↦ ⌊t * J x⌋₊
  set e := Fintype.equivFin (Σ x : sumTriples N, Fin (C x))
  refine ⟨_, fun r ↦ (e.symm r).1, fun r ↦ (e.symm r).1.2, ?_⟩
  intro g k
  have hcard : #{r | g (e.symm r).1 = k} = ∑ x ∈ sumTriples N with g x = k, C x := by
    rw [card_equiv e.symm (t := {s | g s.1 = k}) (by simp), card_filter, Fintype.sum_sigma,
      sum_filter, ← sum_coe_sort (sumTriples N)]
    simp [apply_ite card]
  rw [hcard, marginal, mul_sum]
  push_cast
  refine ⟨?_, ?_⟩
  · have h : ∑ x ∈ sumTriples N with g x = k, (t * J x - 1) ≤
        ∑ x ∈ sumTriples N with g x = k, (C x : ℝ) := by
      apply sum_le_sum
      intro x _
      exact (Nat.sub_one_lt_floor _).le
    rw [sum_sub_distrib, sum_const, nsmul_one] at h
    have hsub : (#{x ∈ sumTriples N | g x = k} : ℝ) ≤ #(sumTriples N) := by
      exact_mod_cast card_filter_le _ _
    linarith
  · apply sum_le_sum
    intro x _
    exact Nat.floor_le (mul_nonneg ht (hJ x))

/-- Extending the vectors of a multicolored sum-free family by zero coordinates keeps it
multicolored sum-free. -/
lemma IsMulticoloredSumFree.extend {ι G : Type*} [AddCommGroup G] {x y z : ι → Fin n → G}
    (h : IsMulticoloredSumFree x y z) {d : ℕ} (hnd : n ≤ d) :
    IsMulticoloredSumFree (fun i ↦ Function.extend (Fin.castLE hnd) (x i) 0)
      (fun i ↦ Function.extend (Fin.castLE hnd) (y i) 0)
      fun i ↦ Function.extend (Fin.castLE hnd) (z i) 0 :=
  h.map (Function.ExtendByZero.hom G (Fin.castLE hnd))
    (Function.extend_injective (Fin.castLE_injective hnd) 0)

/-- For `a > 0`, `b √(d + 1) ≤ a d` for every large `d`. -/
lemma exists_forall_ge_mul_sqrt_le {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, b * √(d + 1) ≤ a * d := by
  refine ⟨⌈(2 * b / a) ^ 2⌉₊ + 1, ?_⟩
  intro d hd
  have hd' : (2 * b / a) ^ 2 + 1 ≤ d := by
    have h : ((⌈(2 * b / a) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at h
    linarith [Nat.le_ceil ((2 * b / a) ^ 2)]
  have hb : 2 * b / a ≤ √(d + 1) := (le_abs_self _).trans (abs_le_sqrt (by linarith))
  rw [div_le_iff₀ ha] at hb
  have h := mul_le_mul_of_nonneg_right (by linarith : b ≤ a / 2 * √(d + 1)) (sqrt_nonneg (d + 1))
  rw [mul_assoc, mul_self_sqrt (by positivity)] at h
  linarith [mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ d) ha.le]

/-- **A family in every large dimension.** For `p ≥ 2` there are constants `T` and `K` such that
for every `d ≥ T + 1` there are `n ∈ [d - T, d]` and a multicolored sum-free family in
`Fin d → ZMod p` with at least
`exp (n (1 - c p) log p - K - p log (n + 1) - 4 √(log ((36 + 2 p) p ^ (3 n)))) / (4 (36 + 2 p))`
members. -/
lemma exists_isMulticoloredSumFree_exp_le {p : ℕ} (hp : 2 ≤ p) :
    ∃ T K : ℝ, 0 ≤ T ∧ ∀ d : ℕ, T + 1 ≤ d → ∃ (n m : ℕ) (x y z : Fin m → Fin d → ZMod p),
      IsMulticoloredSumFree x y z ∧ d - T ≤ n ∧ n ≤ d ∧
        exp (n * ((1 - c p) * log p) - K - p * log (n + 1) -
          4 * √(log ((36 + 2 * p) * p ^ (3 * n)))) / (4 * (36 + 2 * p)) ≤ m := by
  obtain ⟨N, hpN⟩ : ∃ N, p = N + 1 := ⟨p - 1, by grind⟩
  have hpN' : (N : ℝ) + 1 = p := by rw [hpN]; push_cast; ring
  obtain ⟨ρ, hρ₀, hρ₁, hmean, J, hJ, h₁, h₂, h₃⟩ := exists_compatible_geom (N := N) (by grind)
  set G := ∑ k ∈ range (N + 1), ρ ^ k
  have hG : 0 < G := sum_pos (fun k _ ↦ pow_pos hρ₀ k) nonempty_range_add_one
  set T := ((#(sumTriples N) : ℕ) : ℝ)
  have hT : 0 ≤ T := Nat.cast_nonneg _
  refine ⟨p * T, p * (1 + (p * T) ^ 2 * G / ρ ^ N) - T * N * p * log ρ, by positivity, ?_⟩
  intro d hd
  obtain ⟨n, f₀, hf₀, hcount⟩ := exists_base (N := N) hJ (div_nonneg d.cast_nonneg hG.le)
  have hD (g : ℕ × ℕ × ℕ → ℕ) (hg : marginal N J g = geom N ρ) (k : ℕ) (hk : k ∈ range (N + 1)) :
      d / G * ρ ^ k - T ≤ #{r | g (f₀ r) = k} ∧ (#{r | g (f₀ r) = k} : ℝ) ≤ d / G * ρ ^ k := by
    rw [← (by simp [hg, geom, mem_range_succ_iff.1 hk] : marginal N J g k = ρ ^ k)]
    exact hcount g k
  have hsum (r : Fin n) : (f₀ r).1 + (f₀ r).2.1 + (f₀ r).2.2 = N := mem_sumTriples.1 (hf₀ r)
  obtain ⟨hn₁, hn₂⟩ := card_bounds (fun r ↦ by grind [hsum r]) (hD _ h₁)
  rw [div_mul_cancel₀ _ hG.ne'] at hn₁ hn₂
  rw [hpN'] at hn₁
  have hn : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
  have hc : (1 - c p) * log p ≤ log G - N / 3 * log ρ := by
    have h := rpow_one_sub_c_le hp hρ₀ hρ₁
    rw [hpN] at h
    have h' := log_le_log (by positivity) h
    rw [log_rpow (by positivity), log_mul (by positivity) hG.ne', log_rpow hρ₀] at h'
    rw [hpN]
    push_cast at h' ⊢
    linarith
  set w := max 1 (exp (n * ((1 - c p) * log p) -
    (p * (1 + (p * T) ^ 2 * G / ρ ^ N) - T * N * p * log ρ) - p * log (n + 1)))
  have hW (g : ℕ × ℕ × ℕ → ℕ) (hga : ∀ r, g (f₀ r) ≤ N) (hg : marginal N J g = geom N ρ) :
      w ≤ #(typeClass fun r ↦ g (f₀ r)) := by
    have hpos : (1 : ℝ) ≤ #(typeClass fun r ↦ g (f₀ r)) :=
      Nat.one_le_cast.2 (card_pos.2 ⟨_, mem_typeClass.2 ⟨1, rfl⟩⟩)
    refine max_le hpos ?_
    rw [← le_log_iff_exp_le (by linarith)]
    have h := le_log_card_typeClass_geom hρ₀ hρ₁ hmean hT _ hga hn (hD g hg)
    rw [hpN'] at h
    linarith [mul_le_mul_of_nonneg_left hc n.cast_nonneg]
  obtain ⟨m, x, y, z, hsf, hm⟩ := exists_isMulticoloredSumFree_of_typeClass (w := w) hp
    (fun r ↦ by grind [hsum r]) (le_max_left _ _) (hW (·.1) (fun r ↦ by grind [hsum r]) h₁)
    (hW (·.2.1) (fun r ↦ by grind [hsum r]) h₂) (hW (·.2.2) (fun r ↦ by grind [hsum r]) h₃)
  have hnd : n ≤ d := by exact_mod_cast hn₂
  refine ⟨n, m, _, _, _, hsf.extend hnd, by linarith, hnd, ?_⟩
  grw [← hm]
  rw [div_le_div_iff_of_pos_right (by positivity), sub_eq_add_neg _ (4 * √_), exp_add, ← neg_mul]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le

/-- **Large multicolored sum-free families** (Kleinberg, Sawin and Speyer, using Pebody's theorem;
the second part of Theorem 2 of Fox and Lovász). For `p ≥ 2` and `η > 0`, every large `n` has a
multicolored sum-free family in `Fin n → ZMod p` with at least `p ^ ((1 - c p - η) n)` members. -/
theorem exists_forall_ge_exists_isMulticoloredSumFree {p : ℕ} (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p),
      IsMulticoloredSumFree x y z ∧ (p : ℝ) ^ ((1 - c p - η) * n) ≤ m := by
  obtain ⟨T, K, hT, hfam⟩ := exists_isMulticoloredSumFree_exp_le hp
  have hlogp : 0 < log p := log_pos (by exact_mod_cast hp)
  set B := log (36 + 2 * p) + 3 * log p
  set A := (1 - c p) * log p * T + K + log (4 * (36 + 2 * p))
  have hB₁ : 0 ≤ log (36 + 2 * p) := log_nonneg (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
  obtain ⟨d₀, hd₀⟩ := exists_forall_ge_mul_sqrt_le (mul_pos hη hlogp) (|A| + 2 * p + 4 * √B)
  refine ⟨max d₀ (⌈T⌉₊ + 1), ?_⟩
  intro d hd
  have hTd : T + 1 ≤ d := by
    have h : ((⌈T⌉₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast le_of_max_le_right hd
    push_cast at h
    linarith [Nat.le_ceil T]
  obtain ⟨n, m, x, y, z, hsf, hn₁, hn₂, hm⟩ := hfam d hTd
  have hn₂' : (n : ℝ) ≤ d := by exact_mod_cast hn₂
  refine ⟨m, x, y, z, hsf, ?_⟩
  grw [← hm]
  rw [rpow_def_of_pos (by positivity), le_div_iff₀ (by positivity),
    ← exp_log (by positivity : (0 : ℝ) < 4 * (36 + 2 * p)), ← exp_add, exp_le_exp]
  have hlog : log (n + 1) ≤ 2 * √(d + 1) := by
    have h := log_le_rpow_div (by positivity : (0 : ℝ) ≤ d + 1) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← sqrt_eq_rpow] at h
    grw [log_le_log (by positivity) (by linarith : (n : ℝ) + 1 ≤ d + 1)]
    linarith
  have hsq : √(log ((36 + 2 * p) * p ^ (3 * n))) ≤ √B * √(d + 1) := by
    rw [← sqrt_mul (by positivity)]
    apply sqrt_le_sqrt
    rw [log_mul (by positivity) (by positivity), log_pow]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hn₂' hlogp.le, mul_nonneg hB₁ d.cast_nonneg,
      mul_nonneg hlogp.le d.cast_nonneg]
  have hA : A ≤ |A| * √(d + 1) :=
    (le_abs_self A).trans (le_mul_of_one_le_right (abs_nonneg A) (one_le_sqrt.2 (by simp)))
  linarith [hd₀ d (le_of_max_le_left hd), mul_le_mul_of_nonneg_right hn₁
    (mul_nonneg (sub_nonneg.2 (c_lt_one hp).le) hlogp.le),
    mul_le_mul_of_nonneg_left hlog p.cast_nonneg]

end ArithmeticTriangleRemovalInVectorSpaces
