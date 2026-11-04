/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.Coupling.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Peeling off the layer where the first variable vanishes

This file contains the induction step of Pebody's proof that decreasing mass functions on
`[0, N]` whose means sum to `N` are compatible. If the second and the third mass functions vanish
at `N`, then the mass of the first one at `0` can be matched with pairs `(k, N - k)` so that what
remains is again decreasing, at level `N - 1`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn N π`: `π` is a nonnegative, antitone
  mass function vanishing beyond `N`.
* `ArithmeticTriangleRemovalInVectorSpaces.mass N π` and
  `ArithmeticTriangleRemovalInVectorSpaces.moment N π`: the total mass and the first moment.
* `ArithmeticTriangleRemovalInVectorSpaces.DecreasingCompatible N`: the statement of Pebody's
  theorem at level `N`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.le_sum_min`: Lemma 3.1 of Pebody.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_of_eq_zero_of_eq_zero`: Corollary 3.2 of
  Pebody.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- A mass function on `ℕ` is decreasing on `[0, N]` if it is nonnegative, antitone and vanishes at
`N + 1`. -/
structure IsDecreasingOn (N : ℕ) (π : ℕ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ π k
  antitone : Antitone π
  eq_zero : π (N + 1) = 0

/-- The total mass of `π` on `[0, N]`. -/
@[expose] def mass (N : ℕ) (π : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), π k

/-- The first moment of `π` on `[0, N]`. -/
@[expose] def moment (N : ℕ) (π : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), k * π k

/-- Pebody's theorem at level `N`: decreasing mass functions on `[0, N]` with equal masses whose
means sum to `N` are compatible. -/
@[expose] def DecreasingCompatible (N : ℕ) : Prop :=
  ∀ π₁ π₂ π₃ : ℕ → ℝ, IsDecreasingOn N π₁ → IsDecreasingOn N π₂ → IsDecreasingOn N π₃ →
    mass N π₂ = mass N π₁ → mass N π₃ = mass N π₁ →
    moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁ → Compatible N π₁ π₂ π₃

variable {N : ℕ} {π π₁ π₂ π₃ : ℕ → ℝ}

lemma IsDecreasingOn.eq_zero_of_lt (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) : π k = 0 :=
  le_antisymm (h.eq_zero ▸ h.antitone hk) (h.nonneg k)

lemma IsDecreasingOn.le_mass (h : IsDecreasingOn N π) (k : ℕ) : π k ≤ mass N π := by
  by_cases hk : k ≤ N
  · exact single_le_sum (fun i _ ↦ h.nonneg i) (mem_range.2 (by grind))
  · rw [h.eq_zero_of_lt (by grind)]
    exact sum_nonneg fun i _ ↦ h.nonneg i

/-- Decreasing weights on `[s, e]` have mean at most `(s + e) / 2`. -/
lemma two_mul_sum_Icc_le (hπ : Antitone π) (s e : ℕ) :
    2 * ∑ k ∈ Icc s e, (k : ℝ) * π k ≤ (s + e) * ∑ k ∈ Icc s e, π k := by
  have hrefl : ∑ k ∈ Icc s e, ((s + e - 2 * k : ℝ) * π k) =
      ∑ k ∈ Icc s e, ((2 * k - (s + e) : ℝ) * π (s + e - k)) := by
    refine sum_nbij' (fun k ↦ s + e - k) (fun k ↦ s + e - k) ?_ ?_ ?_ ?_ ?_
    any_goals intro k hk; simp only [mem_Icc] at hk ⊢; grind
    intro k hk
    simp only [mem_Icc] at hk
    rw [Nat.sub_sub_self (by grind), Nat.cast_sub (by grind)]
    push_cast
    ring
  have hterm (k) (hk : k ∈ Icc s e) : (2 * k - (s + e) : ℝ) * (π k - π (s + e - k)) ≤ 0 := by
    rcases le_total (2 * k) (s + e) with h | h
    · have h' : (2 * k : ℝ) ≤ s + e := by exact_mod_cast h
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (sub_nonneg.2 (hπ (by grind : k ≤ s + e - k)))
    · have h' : (s + e : ℝ) ≤ 2 * k := by exact_mod_cast h
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (sub_nonpos.2 (hπ (by grind : s + e - k ≤ k)))
  have hA : ∑ k ∈ Icc s e, ((2 * k - (s + e) : ℝ) * π k) =
      2 * ∑ k ∈ Icc s e, (k : ℝ) * π k - (s + e) * ∑ k ∈ Icc s e, π k := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    congr with k
    ring
  have hB : ∑ k ∈ Icc s e, ((s + e - 2 * k : ℝ) * π k) =
      (s + e) * ∑ k ∈ Icc s e, π k - 2 * ∑ k ∈ Icc s e, (k : ℝ) * π k := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    congr with k
    ring
  have hC : ∑ k ∈ Icc s e, (2 * k - (s + e) : ℝ) * (π k - π (s + e - k)) =
      ∑ k ∈ Icc s e, ((2 * k - (s + e) : ℝ) * π k) -
        ∑ k ∈ Icc s e, ((2 * k - (s + e) : ℝ) * π (s + e - k)) := by
    rw [← sum_sub_distrib]
    congr with k
    ring
  linarith [sum_nonpos hterm]

/-- For a decreasing mass function `π` on `[0, N]` and `t ≤ N`, the bound
`2 * moment N π ≤ t * mass N π + (N + 1) * π (t, N]`. -/
lemma IsDecreasingOn.two_mul_moment_le (h : IsDecreasingOn N π) {t : ℕ} (ht : t ≤ N) :
    2 * moment N π ≤ t * mass N π + (N + 1) * ∑ k ∈ Ico (t + 1) (N + 1), π k := by
  have hrange : range (t + 1) = Icc 0 t := by
    ext k
    simp only [mem_range, mem_Icc]
    grind
  have hIco : Ico (t + 1) (N + 1) = Icc (t + 1) N := by
    ext k
    simp only [mem_Ico, mem_Icc]
    grind
  have hsplit (f : ℕ → ℝ) : ∑ k ∈ range (N + 1), f k =
      ∑ k ∈ Icc 0 t, f k + ∑ k ∈ Icc (t + 1) N, f k := by
    rw [← sum_range_add_sum_Ico _ (by grind : t + 1 ≤ N + 1), hrange, hIco]
  have h₁ := two_mul_sum_Icc_le h.antitone 0 t
  have h₂ := two_mul_sum_Icc_le h.antitone (t + 1) N
  rw [moment, mass, hsplit, hsplit, hIco]
  push_cast at h₁ h₂ ⊢
  nlinarith [sum_nonneg fun k (_ : k ∈ Icc (t + 1) N) ↦ h.nonneg k]

/-- **Lemma 3.1 of Pebody**, for a cut `t < N`. -/
lemma le_sum_Ico_add_sum_Ico (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂)
    (h₃ : IsDecreasingOn N π₃) (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) {t : ℕ} (ht : t + 1 ≤ N) :
    π₁ 0 ≤ ∑ k ∈ Ico (t + 1) (N + 1), π₂ k + ∑ k ∈ Ico (N - t) (N + 1), π₃ k := by
  have e₁ := h₁.two_mul_moment_le (Nat.zero_le N)
  have e₂ := h₂.two_mul_moment_le (by grind : t ≤ N)
  have e₃ := h₃.two_mul_moment_le (by grind : N - 1 - t ≤ N)
  rw [(by grind : N - 1 - t + 1 = N - t)] at e₃
  have hm : ∑ k ∈ Ico 1 (N + 1), π₁ k = mass N π₁ - π₁ 0 := by
    rw [mass, ← sum_range_add_sum_Ico _ (by grind : 1 ≤ N + 1)]
    simp
  rw [zero_add, hm] at e₁
  rw [Nat.cast_sub (by grind), Nat.cast_sub (by grind)] at e₃
  push_cast at e₁ e₂ e₃
  have key : (N + 1 : ℝ) * π₁ 0 ≤ (N + 1) *
      (∑ k ∈ Ico (t + 1) (N + 1), π₂ k + ∑ k ∈ Ico (N - t) (N + 1), π₃ k) := by
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- **Lemma 3.1 of Pebody.** The mass of `π₁` at `0` is at most the overlap
`∑ k, min (π₂ k) (π₃ (N - k))`. -/
lemma le_sum_min (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂) (h₃ : IsDecreasingOn N π₃)
    (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) :
    π₁ 0 ≤ ∑ k ∈ range (N + 1), min (π₂ k) (π₃ (N - k)) := by
  set A := (range (N + 1)).filter fun k ↦ π₃ (N - k) ≤ π₂ k
  have hdown {i k : ℕ} (hk : k ∈ A) (hik : i ≤ k) : i ∈ A := by
    simp only [A, mem_filter, mem_range] at hk ⊢
    exact ⟨by grind, (h₃.antitone (by grind)).trans (hk.2.trans (h₂.antitone hik))⟩
  have hA : A = range #A := by
    refine (eq_of_subset_of_card_le ?_ (by simp)).symm
    intro i hi
    by_contra hiA
    have hsub : A ⊆ range i := fun k hk ↦ mem_range.2 (by
      by_contra hki
      exact hiA (hdown hk (by grind)))
    have := card_le_card hsub
    simp only [card_range, mem_range] at this hi
    grind
  have hAN : #A ≤ N + 1 := by
    simpa using card_le_card (filter_subset _ (range (N + 1)))
  have hsum : ∑ k ∈ range (N + 1), min (π₂ k) (π₃ (N - k)) =
      ∑ k ∈ range #A, π₃ (N - k) + ∑ k ∈ Ico #A (N + 1), π₂ k := by
    rw [← sum_range_add_sum_Ico _ hAN]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
      congr with k
      exact min_eq_right (mem_filter.1 ((Finset.ext_iff.1 hA k).2 (mem_range.2 k.isLt))).2
    · rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range,
        ← Fin.sum_univ_eq_sum_range]
      congr with k
      have hk := k.isLt
      have : #A + k ∉ A := by
        intro h
        grind [mem_range.1 ((Finset.ext_iff.1 hA _).1 h)]
      simp only [A, mem_filter, mem_range, not_and, not_le] at this hk
      exact min_eq_left (this (by grind)).le
  rw [hsum]
  rcases Nat.eq_zero_or_pos #A with h0 | hpos
  · rw [h0, range_zero, sum_empty, zero_add, ← range_eq_Ico, ← mass, hm₂]
    exact h₁.le_mass 0
  by_cases hfull : #A = N + 1
  · rw [hfull, Ico_self, sum_empty, add_zero]
    have := sum_range_reflect π₃ (N + 1)
    simp only [add_tsub_cancel_right] at this
    rw [this, ← mass, hm₃]
    exact h₁.le_mass 0
  obtain ⟨t, ht⟩ : ∃ t, #A = t + 1 := ⟨#A - 1, by grind⟩
  have hrefl : ∑ k ∈ range #A, π₃ (N - k) = ∑ k ∈ Ico (N - t) (N + 1), π₃ k := by
    refine sum_nbij' (fun k ↦ N - k) (fun k ↦ N - k) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
    all_goals intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; grind
  rw [hrefl, ht, add_comm]
  exact le_sum_Ico_add_sum_Ico (t := t) h₁ h₂ h₃ hm₂ hm₃ hmom (by grind)

lemma min_min_eq_left_of_lt {a b c d : ℝ} (h : min (min a b) c < d) (hb : d ≤ b) (hc : d ≤ c) :
    min (min a b) c = a := by
  grind

lemma min_min_eq_middle_of_lt {a b c d : ℝ} (h : min (min a b) c < d) (ha : d ≤ a) (hc : d ≤ c) :
    min (min a b) c = b := by
  grind

/-- The overlap of `π₂` and `π₃` at height `x`, used to peel off the layer where the first variable
vanishes. -/
noncomputable def peelWeight (N : ℕ) (π₂ π₃ : ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  min (min (π₂ k) (π₃ (N - k))) x

lemma continuous_sum_peelWeight (N : ℕ) (π₂ π₃ : ℕ → ℝ) :
    Continuous fun x ↦ ∑ k ∈ range (N + 1), peelWeight N π₂ π₃ x k := by
  unfold peelWeight
  fun_prop

/-- There is a height `x ∈ [0, mass N π₁]` at which the overlap of `π₂` and `π₃` has mass `π₁ 0`. -/
lemma exists_sum_peelWeight_eq (h₁ : IsDecreasingOn N π₁) (h₂ : IsDecreasingOn N π₂)
    (h₃ : IsDecreasingOn N π₃) (hm₂ : mass N π₂ = mass N π₁) (hm₃ : mass N π₃ = mass N π₁)
    (hmom : moment N π₁ + moment N π₂ + moment N π₃ = N * mass N π₁) :
    ∃ x, 0 ≤ x ∧ ∑ k ∈ range (N + 1), peelWeight N π₂ π₃ x k = π₁ 0 := by
  have hM : 0 ≤ mass N π₁ := sum_nonneg fun k _ ↦ h₁.nonneg k
  have h0 : ∑ k ∈ range (N + 1), peelWeight N π₂ π₃ 0 k = 0 :=
    sum_eq_zero fun k _ ↦ min_eq_right (le_min (h₂.nonneg k) (h₃.nonneg _))
  have hM' : ∑ k ∈ range (N + 1), peelWeight N π₂ π₃ (mass N π₁) k =
      ∑ k ∈ range (N + 1), min (π₂ k) (π₃ (N - k)) := by
    congr with k
    exact min_eq_left ((min_le_left _ _).trans (hm₂ ▸ h₂.le_mass k))
  obtain ⟨x, hx, hxeq⟩ := intermediate_value_Icc hM (continuous_sum_peelWeight N π₂ π₃).continuousOn
    ⟨h0 ▸ h₁.nonneg 0, hM' ▸ le_sum_min h₁ h₂ h₃ hm₂ hm₃ hmom⟩
  exact ⟨x, hx.1, hxeq⟩

variable {n : ℕ}

/-- The first mass function after peeling: `π₁` shifted down by one. -/
lemma IsDecreasingOn.shift (h : IsDecreasingOn (n + 1) π) :
    IsDecreasingOn n fun k ↦ π (k + 1) :=
  ⟨fun k ↦ h.nonneg _, fun _ _ hab ↦ h.antitone (by grind), h.eq_zero_of_lt (by grind)⟩

section Peel

variable {x : ℝ} (hx : 0 ≤ x) (h₂ : IsDecreasingOn (n + 1) π₂) (h₃ : IsDecreasingOn (n + 1) π₃)
  (h₂N : π₂ (n + 1) = 0) (h₃N : π₃ (n + 1) = 0)
include hx h₂ h₃

lemma peelWeight_nonneg (k : ℕ) : 0 ≤ peelWeight (n + 1) π₂ π₃ x k :=
  le_min (le_min (h₂.nonneg k) (h₃.nonneg _)) hx

include h₂N in
lemma peelWeight_eq_zero_of_lt {k : ℕ} (hk : n + 1 ≤ k) : peelWeight (n + 1) π₂ π₃ x k = 0 := by
  have : π₂ k = 0 := by
    rcases hk.lt_or_eq with hk | rfl
    · exact h₂.eq_zero_of_lt hk
    · exact h₂N
  refine le_antisymm ?_ (peelWeight_nonneg hx h₂ h₃ k)
  exact ((min_le_left _ _).trans (min_le_left _ _)).trans this.le

include h₃N in
lemma peelWeight_zero : peelWeight (n + 1) π₂ π₃ x 0 = 0 :=
  le_antisymm (((min_le_left _ _).trans (min_le_right _ _)).trans (by simp [h₃N]))
    (peelWeight_nonneg hx h₂ h₃ 0)

include h₂N in
lemma isDecreasingOn_sub_peelWeight :
    IsDecreasingOn n fun k ↦ π₂ k - peelWeight (n + 1) π₂ π₃ x k := by
  refine ⟨fun k ↦ sub_nonneg.2 ((min_le_left _ _).trans (min_le_left _ _)), ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro k
    by_cases hle : peelWeight (n + 1) π₂ π₃ x k ≤ peelWeight (n + 1) π₂ π₃ x (k + 1)
    · linarith [h₂.antitone (Nat.le_succ k)]
    · have heq : peelWeight (n + 1) π₂ π₃ x (k + 1) = π₂ (k + 1) := by
        refine min_min_eq_left_of_lt (not_le.1 hle) ?_ ((min_le_right _ _))
        exact ((min_le_left _ _).trans (min_le_right _ _)).trans (h₃.antitone (by grind))
      rw [heq, sub_self]
      exact sub_nonneg.2 ((min_le_left _ _).trans (min_le_left _ _))
  · rw [h₂N, peelWeight_eq_zero_of_lt hx h₂ h₃ h₂N le_rfl, sub_zero]

include h₂N h₃N in
lemma isDecreasingOn_sub_peelWeight_reflect :
    IsDecreasingOn n fun c ↦ π₃ c - peelWeight (n + 1) π₂ π₃ x (n + 1 - c) := by
  have hle (c : ℕ) : peelWeight (n + 1) π₂ π₃ x (n + 1 - c) ≤ π₃ c := by
    by_cases hc : c ≤ n + 1
    · refine ((min_le_left _ _).trans (min_le_right _ _)).trans ?_
      rw [Nat.sub_sub_self hc]
    · rw [(by grind : n + 1 - c = 0), peelWeight_zero hx h₂ h₃ h₃N]
      exact h₃.nonneg c
  refine ⟨fun c ↦ sub_nonneg.2 (hle c), ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro c
    by_cases hc : n + 1 ≤ c
    · rw [(by grind : n + 1 - (c + 1) = 0), peelWeight_zero hx h₂ h₃ h₃N,
        h₃.eq_zero_of_lt (by grind : n + 1 < c + 1), sub_zero]
      exact sub_nonneg.2 (hle c)
    obtain ⟨k, rfl⟩ : ∃ k, n = c + k := ⟨n - c, by grind⟩
    have hlec := hle c
    rw [(by grind : c + k + 1 - c = k + 1)] at hlec
    rw [(by grind : c + k + 1 - (c + 1) = k), (by grind : c + k + 1 - c = k + 1)]
    by_cases hle' : peelWeight (c + k + 1) π₂ π₃ x (k + 1) ≤ peelWeight (c + k + 1) π₂ π₃ x k
    · linarith [h₃.antitone (Nat.le_succ c)]
    · have heq : peelWeight (c + k + 1) π₂ π₃ x k = π₃ (c + 1) := by
        rw [peelWeight, min_min_eq_middle_of_lt (not_le.1 hle') ?_ (min_le_right _ _)]
        · congr 1
          grind
        · exact ((min_le_left _ _).trans (min_le_left _ _)).trans (h₂.antitone (by grind))
      rw [heq, sub_self]
      exact sub_nonneg.2 hlec
  · rw [h₃N, Nat.sub_self, peelWeight_zero hx h₂ h₃ h₃N, sub_zero]

end Peel

/-- **Corollary 3.2 of Pebody.** If Pebody's theorem holds at level `n`, then decreasing mass
functions at level `n + 1` whose second and third members vanish at `n + 1` are compatible. -/
lemma compatible_of_eq_zero_of_eq_zero (ih : DecreasingCompatible n)
    (h₁ : IsDecreasingOn (n + 1) π₁) (h₂ : IsDecreasingOn (n + 1) π₂)
    (h₃ : IsDecreasingOn (n + 1) π₃) (h₂N : π₂ (n + 1) = 0) (h₃N : π₃ (n + 1) = 0)
    (hm₂ : mass (n + 1) π₂ = mass (n + 1) π₁) (hm₃ : mass (n + 1) π₃ = mass (n + 1) π₁)
    (hmom : moment (n + 1) π₁ + moment (n + 1) π₂ + moment (n + 1) π₃ =
      (n + 1 : ℕ) * mass (n + 1) π₁) :
    Compatible (n + 1) π₁ π₂ π₃ := by
  obtain ⟨x, hx, hsum⟩ := exists_sum_peelWeight_eq h₁ h₂ h₃ hm₂ hm₃ hmom
  set f := peelWeight (n + 1) π₂ π₃ x
  have hf0 : f 0 = 0 := peelWeight_zero hx h₂ h₃ h₃N
  have hfN : f (n + 1) = 0 := peelWeight_eq_zero_of_lt hx h₂ h₃ h₂N le_rfl
  have hreflect (g : ℕ → ℝ) : ∑ c ∈ range (n + 1 + 1), g c * f (n + 1 - c) =
      ∑ k ∈ range (n + 1 + 1), g (n + 1 - k) * f k := by
    refine sum_nbij' (fun c ↦ n + 1 - c) (fun k ↦ n + 1 - k) ?_ ?_ ?_ ?_ ?_
    all_goals intro c hc; simp only [mem_range] at hc ⊢; grind
  have hsum' : ∑ k ∈ range (n + 1 + 1), f k = π₁ 0 := hsum
  have hmass₁ : mass n (fun k ↦ π₁ (k + 1)) = mass (n + 1) π₁ - π₁ 0 := by
    simp only [mass]
    rw [sum_range_succ' π₁ (n + 1)]
    ring
  have hmass₂ : mass n (fun k ↦ π₂ k - f k) = mass (n + 1) π₁ - π₁ 0 := by
    rw [← hm₂, ← hsum']
    simp only [mass, sum_sub_distrib]
    rw [sum_range_succ π₂ (n + 1), sum_range_succ f (n + 1), h₂N, hfN]
    ring
  have hmass₃ : mass n (fun c ↦ π₃ c - f (n + 1 - c)) = mass (n + 1) π₁ - π₁ 0 := by
    have := hreflect fun _ ↦ 1
    simp only [one_mul] at this
    rw [← hm₃, ← hsum', ← this]
    simp only [mass, sum_sub_distrib]
    rw [sum_range_succ π₃ (n + 1), sum_range_succ (fun c ↦ f (n + 1 - c)) (n + 1), Nat.sub_self,
      hf0, h₃N]
    ring
  have hcast : ∑ k ∈ range (n + 1 + 1), ((n + 1 - k : ℕ) : ℝ) * f k =
      ∑ k ∈ range (n + 1 + 1), ((n + 1 : ℝ) - k) * f k := by
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    congr with k
    rw [Nat.cast_sub (by grind [k.is_le])]
    push_cast
    ring
  have hm₁ : moment n (fun k ↦ π₁ (k + 1)) = moment (n + 1) π₁ - (mass (n + 1) π₁ - π₁ 0) := by
    simp only [moment, mass]
    rw [sum_range_succ' (fun k ↦ (k : ℝ) * π₁ k) (n + 1), sum_range_succ' π₁ (n + 1)]
    push_cast
    simp only [add_mul, one_mul, sum_add_distrib]
    ring
  have hm₂' : moment n (fun k ↦ π₂ k - f k) =
      moment (n + 1) π₂ - ∑ k ∈ range (n + 1 + 1), (k : ℝ) * f k := by
    simp only [moment, mul_sub, sum_sub_distrib]
    rw [sum_range_succ (fun k ↦ (k : ℝ) * π₂ k) (n + 1),
      sum_range_succ (fun k ↦ (k : ℝ) * f k) (n + 1), h₂N, hfN]
    ring
  have hm₃' : moment n (fun c ↦ π₃ c - f (n + 1 - c)) =
      moment (n + 1) π₃ - ∑ k ∈ range (n + 1 + 1), ((n + 1 : ℝ) - k) * f k := by
    simp only [moment, mul_sub, sum_sub_distrib]
    rw [← hcast, ← hreflect, sum_range_succ (fun k ↦ (k : ℝ) * π₃ k) (n + 1),
      sum_range_succ (fun c ↦ (c : ℝ) * f (n + 1 - c)) (n + 1), Nat.sub_self, hf0, h₃N]
    ring
  have hf : ∑ k ∈ range (n + 1 + 1), (k : ℝ) * f k +
      ∑ k ∈ range (n + 1 + 1), ((n + 1 : ℝ) - k) * f k = (n + 1) * π₁ 0 := by
    rw [← hsum', mul_sum, ← sum_add_distrib]
    congr with k
    ring
  have hmom' : moment n (fun k ↦ π₁ (k + 1)) + moment n (fun k ↦ π₂ k - f k) +
      moment n (fun c ↦ π₃ c - f (n + 1 - c)) = n * mass n fun k ↦ π₁ (k + 1) := by
    rw [hm₁, hm₂', hm₃', hmass₁]
    push_cast at hmom
    linear_combination hmom - hf
  have hcomp := ih _ _ _ h₁.shift (isDecreasingOn_sub_peelWeight hx h₂ h₃ h₂N)
    (isDecreasingOn_sub_peelWeight_reflect hx h₂ h₃ h₂N h₃N) (hmass₂.trans hmass₁.symm)
    (hmass₃.trans hmass₁.symm) hmom'
  have hlayer := compatible_layer (N := n + 1) (peelWeight_nonneg hx h₂ h₃)
  convert (hcomp.comm₁₃.shift 1).comm₁₃.add hlayer using 1
  · ext a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using hsum.symm
    · simp [(by grind : 1 ≤ a), (by grind : a ≠ 0), Nat.sub_add_cancel ha]
  · ext b
    by_cases hb : b ≤ n + 1
    · simp [hb]
    · simp [hb, peelWeight_eq_zero_of_lt hx h₂ h₃ h₂N (by grind : n + 1 ≤ b)]
  · ext c
    by_cases hc : c ≤ n + 1
    · simp [hc]
    · simp [hc, (by grind : n + 1 - c = 0), peelWeight_zero hx h₂ h₃ h₃N]

end ArithmeticTriangleRemovalInVectorSpaces
