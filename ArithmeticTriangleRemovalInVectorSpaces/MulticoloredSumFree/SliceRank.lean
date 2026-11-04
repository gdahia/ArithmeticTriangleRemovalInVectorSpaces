/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Monomials
import ArithmeticTriangleRemovalInVectorSpaces.SliceRank.Diagonal
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.Finite.Basic

/-!
# The slice rank bound for multicolored sum-free families

The function `[x + y + z = 0]` on `(Fin d → ZMod p) ^ 3` is the product over the coordinates `t`
of `1 - (x t + y t + z t) ^ (p - 1)`, a polynomial of degree at most `(p - 1) * d`. Each of its
monomials has degree at most `(p - 1) * d / 3` in one of `x`, `y` and `z`, so the function has
slice rank at most `3 * #(lowDegreeExponents p d)`. On a multicolored sum-free family it restricts
to a diagonal function, and Tao's lemma bounds the size of the family. This is the argument of
Croot, Lev and Pach, Ellenberg and Gijswijt, and Blasiak, Church, Cohn, Grochow, Naslund, Sawin and
Umans, in the slice rank language of Tao.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_ite_add_add_eq_zero_eq_sum`: the decomposition of
  `[x + y + z = 0]` into `3 * #(lowDegreeExponents p d)` slices.
* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_three_mul_card`: a
  multicolored sum-free family in `Fin d → ZMod p` has at most `3 * #(lowDegreeExponents p d)`
  members.
-/

public section

open Finset MvPolynomial

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {p : ℕ} [Fact p.Prime]

/-- The function `[u + v + w = 0]` on `ZMod p` is a polynomial of degree at most `p - 1`. -/
lemma exists_ite_add_add_eq_zero_eq_sum :
    ∃ S : Finset (Fin 3 →₀ ℕ), ∃ κ : (Fin 3 →₀ ℕ) → ZMod p, (∀ e ∈ S, e 0 + e 1 + e 2 ≤ p - 1) ∧
      ∀ u v w : ZMod p,
        (if u + v + w = 0 then 1 else 0) = ∑ e ∈ S, κ e * (u ^ e 0 * v ^ e 1 * w ^ e 2) := by
  let P : MvPolynomial (Fin 3) (ZMod p) := 1 - (X 0 + X 1 + X 2) ^ (p - 1)
  refine ⟨P.support, fun e ↦ P.coeff e, ?_, ?_⟩
  · intro e he
    have hdeg := le_totalDegree he
    have hP : P.totalDegree ≤ p - 1 := by
      grw [totalDegree_sub, totalDegree_one, totalDegree_pow, totalDegree_add, totalDegree_add,
        totalDegree_X, totalDegree_X, totalDegree_X]
      simp
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_three] at hdeg
    grind
  · intro u v w
    have hP := eval_eq' ![u, v, w] P
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hP
    rw [← hP]
    simp only [P, map_sub, map_one, map_pow, map_add, eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    by_cases h : u + v + w = 0
    · simp [h, zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)]
    · simp [h, ZMod.pow_card_sub_one_eq_one h]

/-- Grouping a sum according to a map into a finite set. -/
lemma sum_mul_eq_sum_mul_sum {κ α R : Type*} [CommSemiring R] [DecidableEq α] {s : Finset κ}
    {A : Finset α} (a : κ → α) (ha : ∀ σ ∈ s, a σ ∈ A) (u : α → R) (v : κ → R) :
    ∑ σ ∈ s, u (a σ) * v σ = ∑ α ∈ A, u α * ∑ σ ∈ s with a σ = α, v σ := by
  rw [← sum_fiberwise_of_maps_to ha]
  congr with α
  rw [mul_sum, sum_filter, sum_filter]
  congr with σ
  grind

variable (p) in
/-- The function `[x + y + z = 0]` on `(Fin d → ZMod p) ^ 3` is a sum of
`3 * #(lowDegreeExponents p d)` slices: products of a monomial `x ^ α`, `y ^ β` or `z ^ γ` of low
degree and a function of the other two variables. -/
lemma exists_ite_eq_sum_slices (d : ℕ) :
    ∃ F G H : (Fin d → ℕ) → (Fin d → ZMod p) → (Fin d → ZMod p) → ZMod p,
      ∀ x y z : Fin d → ZMod p, (if x + y + z = 0 then 1 else 0) =
        ∑ α ∈ lowDegreeExponents p d, (∏ t, x t ^ α t) * F α y z +
        ∑ β ∈ lowDegreeExponents p d, (∏ t, y t ^ β t) * G β x z +
        ∑ γ ∈ lowDegreeExponents p d, (∏ t, z t ^ γ t) * H γ x y := by
  classical
  obtain ⟨S, κ, hS, hf⟩ := exists_ite_add_add_eq_zero_eq_sum (p := p)
  let P := Fintype.piFinset fun _ : Fin d ↦ S
  let a (σ : Fin d → Fin 3 →₀ ℕ) (s : Fin 3) : Fin d → ℕ := fun t ↦ σ t s
  let low (σ : Fin d → Fin 3 →₀ ℕ) (s : Fin 3) : Prop := 3 * ∑ t, a σ s t ≤ (p - 1) * d
  have hsum (σ) (hσ : σ ∈ P) : ∑ t, a σ 0 t + ∑ t, a σ 1 t + ∑ t, a σ 2 t ≤ (p - 1) * d := by
    simp only [a, ← sum_add_distrib]
    grw [sum_le_sum fun t _ ↦ hS _ (Fintype.mem_piFinset.1 hσ t)]
    simp [mul_comm]
  have hmem (σ) (hσ : σ ∈ P) (s : Fin 3) (hs : low σ s) : a σ s ∈ lowDegreeExponents p d := by
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t ↦ mem_range.2 ?_, hs⟩
    have := hS _ (Fintype.mem_piFinset.1 hσ t)
    have := (Fact.out : p.Prime).one_lt
    fin_cases s <;> simp [a] <;> grind
  have hlow (σ) (hσ : σ ∈ (P.filter (¬low · 0)).filter (¬low · 1)) : low σ 2 := by
    simp only [mem_filter] at hσ
    obtain ⟨⟨hσP, h₀⟩, h₁⟩ := hσ
    have := hsum σ hσP
    simp only [low] at *
    grind
  refine ⟨fun α y z ↦ ∑ σ ∈ (P.filter (low · 0)).filter (a · 0 = α),
      ∏ t, κ (σ t) * (y t ^ σ t 1 * z t ^ σ t 2),
    fun β x z ↦ ∑ σ ∈ ((P.filter (¬low · 0)).filter (low · 1)).filter (a · 1 = β),
      ∏ t, κ (σ t) * (x t ^ σ t 0 * z t ^ σ t 2),
    fun γ x y ↦ ∑ σ ∈ ((P.filter (¬low · 0)).filter (¬low · 1)).filter (a · 2 = γ),
      ∏ t, κ (σ t) * (x t ^ σ t 0 * y t ^ σ t 1), ?_⟩
  intro x y z
  have hexp : (if x + y + z = 0 then (1 : ZMod p) else 0) =
      ∑ σ ∈ P, ∏ t, κ (σ t) * (x t ^ σ t 0 * y t ^ σ t 1 * z t ^ σ t 2) := by
    trans ∏ t, ∑ e ∈ S, κ e * (x t ^ e 0 * y t ^ e 1 * z t ^ e 2)
    · simp_rw [← hf]
      rw [prod_boole]
      simp [funext_iff]
    · exact prod_univ_sum _ _
  rw [hexp, ← sum_filter_add_sum_filter_not P (low · 0),
    ← sum_filter_add_sum_filter_not (P.filter (¬low · 0)) (low · 1), add_assoc]
  congr 1
  · rw [← sum_mul_eq_sum_mul_sum (a · 0) fun σ hσ ↦
      hmem σ (mem_filter.1 hσ).1 0 (mem_filter.1 hσ).2]
    congr 1 with σ
    rw [← prod_mul_distrib]
    congr 1 with t
    ring
  congr 1
  · rw [← sum_mul_eq_sum_mul_sum (a · 1) fun σ hσ ↦ hmem σ
      (mem_filter.1 (mem_filter.1 hσ).1).1 1 (mem_filter.1 hσ).2]
    congr 1 with σ
    rw [← prod_mul_distrib]
    congr 1 with t
    ring
  · rw [← sum_mul_eq_sum_mul_sum (a · 2) fun σ hσ ↦ hmem σ
      (mem_filter.1 (mem_filter.1 hσ).1).1 2 (hlow σ hσ)]
    congr 1 with σ
    rw [← prod_mul_distrib]
    congr 1 with t
    ring

/-- **The slice rank bound** for multicolored sum-free families: a multicolored sum-free family in
`Fin d → ZMod p` has at most `3 * #(lowDegreeExponents p d)` members. -/
lemma IsMulticoloredSumFree.card_le_three_mul_card {ι : Type*} [Fintype ι] {d : ℕ}
    {x y z : ι → Fin d → ZMod p} (h : IsMulticoloredSumFree x y z) :
    Fintype.card ι ≤ 3 * #(lowDegreeExponents p d) := by
  classical
  obtain ⟨F, G, H, hT⟩ := exists_ite_eq_sum_slices p d
  have := card_le_card_add_card_add_card (fun α i ↦ ∏ t, x i t ^ α t) (fun α j k ↦ F α (y j) (z k))
    (fun β j ↦ ∏ t, y j t ^ β t) (fun β i k ↦ G β (x i) (z k)) (fun γ k ↦ ∏ t, z k t ^ γ t)
    (fun γ i j ↦ H γ (x i) (y j)) fun i j k ↦ by
      rw [← hT]
      simp [h i j k]
  grind

end ArithmeticTriangleRemovalInVectorSpaces
