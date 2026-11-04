/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compatible mass functions

Three mass functions `π₁`, `π₂` and `π₃` on `ℕ` are compatible at level `N` if they are the
marginals of a nonnegative function on the triples `(a, b, c)` of natural numbers with
`a + b + c = N`. For probability distributions, this says that there are random variables `X₁`,
`X₂` and `X₃` with distributions `π₁`, `π₂` and `π₃` such that `X₁ + X₂ + X₃ = N`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.sumTriples N`: the triples of natural numbers with sum
  `N`.
* `ArithmeticTriangleRemovalInVectorSpaces.marginal N J g`: the push-forward of `J` along `g`.
* `ArithmeticTriangleRemovalInVectorSpaces.Compatible N π₁ π₂ π₃`: `π₁`, `π₂` and `π₃` are
  compatible at level `N`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.Compatible.add` and
  `ArithmeticTriangleRemovalInVectorSpaces.Compatible.smul`: compatible triples form a convex cone.
* `ArithmeticTriangleRemovalInVectorSpaces.Compatible.comm₁₂` and
  `ArithmeticTriangleRemovalInVectorSpaces.Compatible.comm₂₃`: compatibility does not depend on
  the order of the mass functions.
* `ArithmeticTriangleRemovalInVectorSpaces.Compatible.shift`: adding `d` to the third variable
  raises the level by `d`.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_layer`: the triples `(0, b, N - b)` with
  weights `f b`.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The triples `(a, b, c)` of natural numbers with `a + b + c = N`. -/
def sumTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter fun x ↦ x.1 + x.2.1 + x.2.2 = N

@[simp]
lemma mem_sumTriples {N : ℕ} {x : ℕ × ℕ × ℕ} : x ∈ sumTriples N ↔ x.1 + x.2.1 + x.2.2 = N := by
  simp only [sumTriples, mem_filter, mem_product, mem_range]
  grind

/-- The push-forward of `J`, restricted to the triples with sum `N`, along `g`. -/
@[expose] def marginal (N : ℕ) (J : ℕ × ℕ × ℕ → ℝ) (g : ℕ × ℕ × ℕ → ℕ) (k : ℕ) : ℝ :=
  ∑ x ∈ sumTriples N with g x = k, J x

/-- Three mass functions on `ℕ` are compatible at level `N` if they are the marginals of a
nonnegative function on the triples with sum `N`. -/
@[expose] def Compatible (N : ℕ) (π₁ π₂ π₃ : ℕ → ℝ) : Prop :=
  ∃ J : ℕ × ℕ × ℕ → ℝ, (∀ x, 0 ≤ J x) ∧ marginal N J (·.1) = π₁ ∧ marginal N J (·.2.1) = π₂ ∧
    marginal N J (·.2.2) = π₃

variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}

lemma marginal_add : marginal N (J + J') g = marginal N J g + marginal N J' g := by
  ext k
  simp [marginal, sum_add_distrib]

lemma marginal_smul (r : ℝ) : marginal N (r • J) g = r • marginal N J g := by
  ext k
  simp [marginal, mul_sum]

/-- Precomposing `J` with an involution of the triples that preserves the sum amounts to
precomposing `g` with it. -/
lemma marginal_comp {e : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ} (he : ∀ x, e (e x) = x)
    (hsum : ∀ x, (e x).1 + (e x).2.1 + (e x).2.2 = x.1 + x.2.1 + x.2.2) :
    marginal N (J ∘ e) g = marginal N J (g ∘ e) := by
  ext k
  refine sum_nbij' e e ?_ ?_ (fun x _ ↦ he x) (fun x _ ↦ he x) (fun _ _ ↦ rfl)
  all_goals
    intro x hx
    simp only [mem_filter, mem_sumTriples, Function.comp_apply, hsum, he] at hx ⊢
    exact hx

lemma compatible_zero : Compatible N 0 0 0 :=
  ⟨0, fun _ ↦ le_rfl, by ext; simp [marginal], by ext; simp [marginal], by ext; simp [marginal]⟩

lemma Compatible.add (h : Compatible N π₁ π₂ π₃) (h' : Compatible N π₁' π₂' π₃') :
    Compatible N (π₁ + π₁') (π₂ + π₂') (π₃ + π₃') := by
  obtain ⟨J, hJ, h₁, h₂, h₃⟩ := h
  obtain ⟨J', hJ', h₁', h₂', h₃'⟩ := h'
  exact ⟨J + J', fun x ↦ add_nonneg (hJ x) (hJ' x), by rw [marginal_add, h₁, h₁'],
    by rw [marginal_add, h₂, h₂'], by rw [marginal_add, h₃, h₃']⟩

lemma Compatible.smul (h : Compatible N π₁ π₂ π₃) {r : ℝ} (hr : 0 ≤ r) :
    Compatible N (r • π₁) (r • π₂) (r • π₃) := by
  obtain ⟨J, hJ, h₁, h₂, h₃⟩ := h
  exact ⟨r • J, fun x ↦ mul_nonneg hr (hJ x), by rw [marginal_smul, h₁],
    by rw [marginal_smul, h₂], by rw [marginal_smul, h₃]⟩

lemma Compatible.comm₁₂ (h : Compatible N π₁ π₂ π₃) : Compatible N π₂ π₁ π₃ := by
  obtain ⟨J, hJ, h₁, h₂, h₃⟩ := h
  have hcomp (g) := marginal_comp (N := N) (J := J) (g := g) (e := fun x ↦ (x.2.1, x.1, x.2.2))
    (fun _ ↦ rfl) (fun _ ↦ by ring)
  exact ⟨J ∘ fun x ↦ (x.2.1, x.1, x.2.2), fun x ↦ hJ _, by rw [hcomp]; exact h₂,
    by rw [hcomp]; exact h₁, by rw [hcomp]; exact h₃⟩

lemma Compatible.comm₂₃ (h : Compatible N π₁ π₂ π₃) : Compatible N π₁ π₃ π₂ := by
  obtain ⟨J, hJ, h₁, h₂, h₃⟩ := h
  have hcomp (g) := marginal_comp (N := N) (J := J) (g := g) (e := fun x ↦ (x.1, x.2.2, x.2.1))
    (fun _ ↦ rfl) (fun _ ↦ by ring)
  exact ⟨J ∘ fun x ↦ (x.1, x.2.2, x.2.1), fun x ↦ hJ _, by rw [hcomp]; exact h₁,
    by rw [hcomp]; exact h₃, by rw [hcomp]; exact h₂⟩

lemma Compatible.comm₁₃ (h : Compatible N π₁ π₂ π₃) : Compatible N π₃ π₂ π₁ :=
  h.comm₁₂.comm₂₃.comm₁₂

/-- The function `J` with `d` added to the third variable. -/
def shiftThird (d : ℕ) (J : ℕ × ℕ × ℕ → ℝ) (x : ℕ × ℕ × ℕ) : ℝ :=
  if d ≤ x.2.2 then J (x.1, x.2.1, x.2.2 - d) else 0

lemma marginal_shiftThird (d : ℕ) (k : ℕ) :
    marginal (N + d) (shiftThird d J) g k =
      ∑ x ∈ sumTriples N with g (x.1, x.2.1, x.2.2 + d) = k, J x := by
  simp only [marginal, shiftThird]
  rw [← sum_filter, filter_filter]
  refine sum_nbij' (fun x ↦ (x.1, x.2.1, x.2.2 - d)) (fun x ↦ (x.1, x.2.1, x.2.2 + d)) ?_ ?_ ?_ ?_
    (fun _ _ ↦ rfl)
  · intro x hx
    simp only [mem_filter, mem_sumTriples] at hx ⊢
    obtain ⟨h₁, h₂, h₃⟩ := hx
    exact ⟨by grind, by rwa [Nat.sub_add_cancel h₃]⟩
  · intro x hx
    simp only [mem_filter, mem_sumTriples] at hx ⊢
    obtain ⟨h₁, h₂⟩ := hx
    exact ⟨by grind, h₂, by grind⟩
  · intro x hx
    simp only [mem_filter, mem_sumTriples] at hx
    obtain ⟨-, -, h₃⟩ := hx
    simp [Nat.sub_add_cancel h₃]
  · intro x _
    simp

/-- Adding `d` to the third variable raises the level by `d`. -/
lemma Compatible.shift (h : Compatible N π₁ π₂ π₃) (d : ℕ) :
    Compatible (N + d) π₁ π₂ fun c ↦ if d ≤ c then π₃ (c - d) else 0 := by
  obtain ⟨J, hJ, h₁, h₂, h₃⟩ := h
  refine ⟨shiftThird d J, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold shiftThird
    grind
  · ext k
    rw [marginal_shiftThird, ← h₁]
    rfl
  · ext k
    rw [marginal_shiftThird, ← h₂]
    rfl
  · ext k
    rw [marginal_shiftThird, ← h₃]
    by_cases hk : d ≤ k
    · simp only [hk, ↓reduceIte]
      rw [marginal]
      congr 1
      ext x
      simp only [mem_filter]
      grind
    · simp only [hk, ↓reduceIte]
      apply sum_eq_zero
      intro x hx
      simp only [mem_filter] at hx
      grind

/-- The triples `(0, b, N - b)` with weights `f b`. -/
lemma compatible_layer {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    Compatible N (fun a ↦ if a = 0 then ∑ k ∈ range (N + 1), f k else 0)
      (fun b ↦ if b ≤ N then f b else 0) fun c ↦ if c ≤ N then f (N - c) else 0 := by
  refine ⟨fun x ↦ if x.1 = 0 then f x.2.1 else 0, ?_, ?_, ?_, ?_⟩
  · intro x
    grind
  · ext a
    simp only [marginal]
    by_cases ha : a = 0
    · simp only [ha, ↓reduceIte]
      subst ha
      rw [sum_ite_of_true (fun x hx ↦ (mem_filter.1 hx).2)]
      refine sum_nbij' (fun x ↦ x.2.1) (fun b ↦ (0, b, N - b)) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
      · intro x hx
        simp only [mem_filter, mem_sumTriples, mem_range] at hx ⊢
        grind
      · intro b hb
        simp at hb ⊢
        grind
      · intro x hx
        simp only [mem_filter, mem_sumTriples] at hx
        ext <;> simp <;> grind
      · intro b _
        rfl
    · simp only [ha, ↓reduceIte]
      apply sum_eq_zero
      intro x hx
      simp [(mem_filter.1 hx).2, ha]
  · ext b
    simp only [marginal]
    by_cases hb : b ≤ N
    · simp only [hb, ↓reduceIte]
      rw [sum_eq_single_of_mem (0, b, N - b) (by simp; grind)]
      · simp
      · intro x hx hne
        simp only [mem_filter, mem_sumTriples] at hx
        grind [Prod.ext_iff]
    · simp only [hb, ↓reduceIte]
      apply sum_eq_zero
      intro x hx
      simp only [mem_filter, mem_sumTriples] at hx
      grind
  · ext c
    simp only [marginal]
    by_cases hc : c ≤ N
    · simp only [hc, ↓reduceIte]
      rw [sum_eq_single_of_mem (0, N - c, c) (by simp; grind)]
      · simp
      · intro x hx hne
        simp only [mem_filter, mem_sumTriples] at hx
        grind [Prod.ext_iff]
    · simp only [hc, ↓reduceIte]
      apply sum_eq_zero
      intro x hx
      simp only [mem_filter, mem_sumTriples] at hx
      grind

end ArithmeticTriangleRemovalInVectorSpaces
