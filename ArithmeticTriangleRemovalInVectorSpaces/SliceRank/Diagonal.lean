/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The slice rank of a diagonal tensor

A function `T : ι → ι → ι → F` has slice rank at most `r` if it is a sum of `r` products, each of
a function of one of the three variables and a function of the other two. This file proves Tao's
lemma: the diagonal function `[i = j = k]` has slice rank `Fintype.card ι`. We only state the
inequality that the polynomial method uses.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_mem_finrank_le_card`: a subspace of `ι → F`
  contains a vector with at least `finrank F W` nonzero coordinates.
* `ArithmeticTriangleRemovalInVectorSpaces.card_le_card_add_card_add_card`: if `[i = j = k]` is a
  sum of `#A + #B + #C` such products, then `Fintype.card ι ≤ #A + #B + #C`.
-/

public section

open Finset Matrix Module

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {ι F : Type*} [Fintype ι] [Field F]

/-- A subspace `W` of `ι → F` contains a vector with at least `finrank F W` nonzero coordinates. -/
lemma exists_mem_finrank_le_card [DecidableEq F] (W : Submodule F (ι → F)) :
    ∃ w ∈ W, finrank F W ≤ #{i | w i ≠ 0} := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_image
    ({s | ∃ w ∈ W, ({i | w i ≠ 0} : Finset ι) = s} : Finset (Finset ι)) card
    ⟨∅, by simpa using ⟨0, W.zero_mem, by simp⟩⟩
  obtain ⟨w, hw, rfl⟩ := (mem_filter.1 hs).2
  refine ⟨w, hw, not_lt.1 ?_⟩
  intro hlt
  let r : W →ₗ[F] ({i | w i ≠ 0} : Finset ι) → F :=
    (LinearMap.funLeft F F Subtype.val).comp W.subtype
  have hker : LinearMap.ker r ≠ ⊥ := by
    intro h
    have := r.finrank_range_add_finrank_ker
    rw [h, finrank_bot, add_zero] at this
    have := (Submodule.finrank_le (LinearMap.range r)).trans_eq (finrank_fintype_fun_eq_card F)
    rw [Fintype.card_coe] at this
    grind
  obtain ⟨⟨v, hvW⟩, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hvs (i : ι) (hi : w i ≠ 0) : v i = 0 := by
    simpa [r] using congr_fun (LinearMap.mem_ker.1 hv) ⟨i, by simpa⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv0 (Subtype.ext (funext h))
  refine (hmax _ (mem_filter.2 ⟨mem_univ _, w + v, W.add_mem hw hvW, rfl⟩)).not_gt
    (card_lt_card ⟨?_, ?_⟩)
  · intro i hi
    simp_all
  · intro h
    have := h (by simp [(by grind : w i₀ = 0), hi₀] : i₀ ∈ ({i | (w + v) i ≠ 0} : Finset ι))
    simp_all

/-- **Tao's lemma** on the slice rank of a diagonal tensor. If the function `[i = j = k]` on
`ι × ι × ι` is a sum of `#A + #B + #C` products, each of a function of one variable and a function
of the other two, then `ι` has at most `#A + #B + #C` elements. -/
lemma card_le_card_add_card_add_card [DecidableEq ι] {α β γ : Type*} {A : Finset α} {B : Finset β}
    {C : Finset γ} (f : α → ι → F) (g : α → ι → ι → F) (f' : β → ι → F) (g' : β → ι → ι → F)
    (f'' : γ → ι → F) (g'' : γ → ι → ι → F)
    (h : ∀ i j k, (if i = j ∧ j = k then 1 else 0 : F) =
      ∑ a ∈ A, f a i * g a j k + ∑ b ∈ B, f' b j * g' b i k + ∑ c ∈ C, f'' c k * g'' c i j) :
    Fintype.card ι ≤ #A + #B + #C := by
  classical
  let L : Matrix A ι F := fun a i ↦ f a i
  obtain ⟨w, hw, hcard⟩ := exists_mem_finrank_le_card (LinearMap.ker L.mulVecLin)
  have hL := L.mulVecLin.finrank_range_add_finrank_ker
  rw [finrank_fintype_fun_eq_card] at hL
  have hrange := (Submodule.finrank_le (LinearMap.range L.mulVecLin)).trans_eq
    (finrank_fintype_fun_eq_card F)
  let P : Matrix ι (B ⊕ C) F :=
    fun j x ↦ x.elim (fun b : B ↦ f' b j) fun c : C ↦ ∑ i, w i * g'' c i j
  let Q : Matrix (B ⊕ C) ι F :=
    fun x k ↦ x.elim (fun b : B ↦ ∑ i, w i * g' b i k) fun c : C ↦ f'' c k
  have hwA (a : α) (ha : a ∈ A) : ∑ i, w i * f a i = 0 := by
    have := congr_fun (LinearMap.mem_ker.1 hw) ⟨a, ha⟩
    change (L *ᵥ w) ⟨a, ha⟩ = 0 at this
    simpa [L, mulVec, dotProduct, mul_comm] using this
  have hPQ : diagonal w = P * Q := by
    ext j k
    have hsum : ∑ i, w i * (if i = j ∧ j = k then 1 else 0 : F) = diagonal w j k := by
      by_cases hjk : j = k <;> simp [diagonal, hjk]
    rw [← hsum, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [P, Q, Sum.elim_inl, Sum.elim_inr]
    rw [sum_coe_sort B fun b ↦ f' b j * ∑ i, w i * g' b i k,
      sum_coe_sort C fun c ↦ (∑ i, w i * g'' c i j) * f'' c k]
    simp_rw [h, mul_add, sum_add_distrib, mul_sum, sum_mul]
    rw [sum_comm, sum_eq_zero fun a ha ↦ by simp_rw [← mul_assoc, ← sum_mul, hwA a ha, zero_mul],
      zero_add, sum_comm, sum_comm (s := univ)]
    congr 1 <;> congr with x <;> congr with i <;> ring
  have hrank := hPQ ▸ (rank_mul_le_left P Q).trans (rank_le_card_width P)
  rw [rank_diagonal, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
    Fintype.card_subtype] at hrank
  have := Fintype.card_coe A
  grind

end ArithmeticTriangleRemovalInVectorSpaces
