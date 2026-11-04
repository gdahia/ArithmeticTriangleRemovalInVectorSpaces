/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel

/-!
# Products of multicolored sum-free families

This is the construction of Section 3 of Fox and Lovász. Let `(x i, y i, z i)` be a multicolored
sum-free family of `m` triples in `G`, and let `X`, `Y` and `Z` be the sets of its first, second and
third vertices. For a finite abelian group `W`, the sets `X × W`, `Y × W` and `Z × W` of `G × W`
contain `m * #W ^ 2` triangles, and removing fewer than `m * #W` of their elements leaves a
triangle. With `G = Fin n → ZMod p` and `W = Fin l → ZMod p`, this shows that the exponent `C p` in
the arithmetic triangle removal lemma cannot be lowered.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_triangles_image`: the sets
  `X`, `Y` and `Z` contain exactly `m` triangles.
* `ArithmeticTriangleRemovalInVectorSpaces.triangles_nonempty_of_card_sdiff_add_lt`: if `m`
  triangles are vertex-disjoint, removing fewer than `m` of their vertices leaves one of them.
* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_triangles_prod`: the sets
  `X × W`, `Y × W` and `Z × W` contain `m * #W ^ 2` triangles.
* `ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.triangles_nonempty`: removing
  fewer than `m * #W` elements from them leaves a triangle.
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {ι G W : Type*} [AddCommGroup G] [AddCommGroup W] {x y z : ι → G}

/-- The first vertices of a multicolored sum-free family are distinct. -/
lemma IsMulticoloredSumFree.injective_left (h : IsMulticoloredSumFree x y z) : Injective x := by
  intro i j hij
  obtain ⟨rfl, -⟩ := (h j i i).1 (hij ▸ (h i i i).2 ⟨rfl, rfl⟩)
  rfl

/-- The second vertices of a multicolored sum-free family are distinct. -/
lemma IsMulticoloredSumFree.injective_middle (h : IsMulticoloredSumFree x y z) : Injective y := by
  intro i j hij
  obtain ⟨rfl, -⟩ := (h i j i).1 (hij ▸ (h i i i).2 ⟨rfl, rfl⟩)
  rfl

/-- The third vertices of a multicolored sum-free family are distinct. -/
lemma IsMulticoloredSumFree.injective_right (h : IsMulticoloredSumFree x y z) : Injective z := by
  intro i j hij
  obtain ⟨-, rfl⟩ := (h i i j).1 (hij ▸ (h i i i).2 ⟨rfl, rfl⟩)
  rfl

section Base

variable [DecidableEq G] [Fintype ι]

/-- The sets `X`, `Y` and `Z` of first, second and third vertices of a multicolored sum-free family
of `m` triples contain exactly `m` triangles. -/
lemma IsMulticoloredSumFree.card_triangles_image (h : IsMulticoloredSumFree x y z) :
    #(triangles (univ.image x) (univ.image y) (univ.image z)) = Fintype.card ι := by
  rw [← card_univ]
  symm
  refine card_bij (fun i _ ↦ (x i, y i, z i)) ?_ ?_ ?_
  · intro i _
    simpa using (h i i i).2 ⟨rfl, rfl⟩
  · intro i _ j _ hij
    simp only [Prod.mk.injEq] at hij
    obtain ⟨hx, -⟩ := hij
    exact h.injective_left hx
  · rintro ⟨g₁, g₂, g₃⟩ ht
    simp only [mem_triangles, mem_image, mem_univ, true_and] at ht
    obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩, hsum⟩ := ht
    obtain ⟨rfl, rfl⟩ := (h i j k).1 hsum
    exact ⟨i, mem_univ _, rfl⟩

/-- Removing fewer than `m` elements from the vertex sets of `m` vertex-disjoint triangles leaves a
triangle. -/
lemma triangles_nonempty_of_card_sdiff_add_lt (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hsum : ∀ i, x i + y i + z i = 0) {X Y Z : Finset G}
    (hcard : #(univ.image x \ X) + #(univ.image y \ Y) + #(univ.image z \ Z) < Fintype.card ι) :
    (triangles X Y Z).Nonempty := by
  classical
  have hle (f : ι → G) (hf : Injective f) (S : Finset G) :
      #({i | f i ∉ S} : Finset ι) ≤ #(univ.image f \ S) :=
    card_le_card_of_injOn f (fun i hi ↦ by simp_all) hf.injOn
  obtain ⟨i, -, hi⟩ := exists_mem_notMem_of_card_lt_card (t := univ)
    (s := (univ.filter fun i ↦ x i ∉ X) ∪ (univ.filter fun i ↦ y i ∉ Y) ∪
      univ.filter fun i ↦ z i ∉ Z) (by
      grw [card_union_le, card_union_le, hle x hx X, hle y hy Y, hle z hz Z, card_univ]
      exact hcard)
  simp only [mem_union, mem_filter, mem_univ, true_and, not_or, not_not] at hi
  obtain ⟨⟨hxi, hyi⟩, hzi⟩ := hi
  exact ⟨_, mem_triangles.2 ⟨hxi, hyi, hzi, hsum i⟩⟩

end Base

variable [DecidableEq G] [DecidableEq W] [Fintype ι] [Fintype W]

/-- The sets `X × W`, `Y × W` and `Z × W` built from a multicolored sum-free family of `m` triples
contain `m * #W ^ 2` triangles. -/
lemma IsMulticoloredSumFree.card_triangles_prod (h : IsMulticoloredSumFree x y z) :
    #(triangles (univ.image x ×ˢ (univ : Finset W)) (univ.image y ×ˢ univ) (univ.image z ×ˢ univ))
      = Fintype.card ι * Fintype.card W ^ 2 := by
  rw [sq, ← Fintype.card_prod, ← Fintype.card_prod, ← card_univ]
  symm
  refine card_bij (fun (i, a, b) _ ↦ ((x i, a), (y i, b), (z i, -(a + b)))) ?_ ?_ ?_
  · rintro ⟨i, a, b⟩ -
    simp only [mem_triangles, mem_product, mem_image, mem_univ, true_and, and_true, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
    refine ⟨⟨i, rfl⟩, ⟨i, rfl⟩, ⟨i, rfl⟩, (h i i i).2 ⟨rfl, rfl⟩, by abel⟩
  · intro s _ t _ hst
    obtain ⟨i, a, b⟩ := s
    obtain ⟨j, a', b'⟩ := t
    simp only [Prod.mk.injEq] at hst
    obtain ⟨⟨hx, rfl⟩, ⟨-, rfl⟩, -⟩ := hst
    rw [h.injective_left hx]
  · rintro ⟨⟨g₁, a⟩, ⟨g₂, b⟩, ⟨g₃, c⟩⟩ ht
    simp only [mem_triangles, mem_product, mem_image, mem_univ, true_and, and_true, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at ht
    obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩, hsum, habc⟩ := ht
    obtain ⟨rfl, rfl⟩ := (h i j k).1 hsum
    refine ⟨(i, a, b), mem_univ _, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    rw [eq_neg_of_add_eq_zero_right habc]

omit [DecidableEq W] in
/-- Three sets of total size more than `2 * #W` contain `a`, `b` and `c` with `a + b + c = 0`. -/
lemma exists_add_add_eq_zero_of_two_mul_card_lt {A B C : Finset W}
    (h : 2 * Fintype.card W < #A + #B + #C) : ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b + c = 0 := by
  classical
  obtain ⟨c, hc⟩ : C.Nonempty := card_pos.1 (by grind [card_le_univ A, card_le_univ B])
  obtain ⟨a, ha⟩ := inter_nonempty_of_card_lt_card_add_card (subset_univ A)
    (subset_univ (B.image fun b ↦ -c - b)) (by
      rw [card_image_of_injective _ fun b b' hb ↦ by simpa using hb, card_univ]
      grind [card_le_univ C])
  obtain ⟨ha, hab⟩ := mem_inter.1 ha
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hab
  exact ⟨_, ha, b, hb, c, hc, by abel⟩

omit [AddCommGroup G] [AddCommGroup W] in
/-- For injective `f`, the fibers of `(univ.image f ×ˢ univ) \ S` over the points `f i` have total
size at most `#((univ.image f ×ˢ univ) \ S)`. -/
lemma sum_card_filter_notMem_le {f : ι → G} (hf : Injective f) (S : Finset (G × W)) :
    ∑ i, #{a | (f i, a) ∉ S} ≤ #((univ.image f ×ˢ univ) \ S) := by
  have hdisj : ((univ : Finset ι) : Set ι).PairwiseDisjoint
      fun i ↦ ({a | (f i, a) ∉ S} : Finset W).image (f i, ·) := by
    rintro i - j - hij
    simp only [Function.onFun, disjoint_left, mem_image]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    obtain ⟨hji, -⟩ := Prod.mk.inj hb
    exact hij (hf hji.symm)
  have hsub : (univ.biUnion fun i ↦ ({a | (f i, a) ∉ S} : Finset W).image (f i, ·)) ⊆
      (univ.image f ×ˢ univ) \ S := by
    intro t ht
    simp only [mem_biUnion, mem_image, mem_filter, mem_univ, true_and] at ht
    obtain ⟨i, a, ha, rfl⟩ := ht
    simp [ha]
  grw [← card_le_card hsub, card_biUnion hdisj]
  simp_rw [card_image_of_injective _ (Prod.mk_right_injective _), le_refl]

/-- Removing fewer than `m * #W` elements from the sets `X × W`, `Y × W` and `Z × W` built from a
multicolored sum-free family of `m` triples leaves a triangle. -/
lemma IsMulticoloredSumFree.triangles_nonempty (h : IsMulticoloredSumFree x y z)
    {X Y Z : Finset (G × W)}
    (hcard : #((univ.image x ×ˢ univ) \ X) + #((univ.image y ×ˢ univ) \ Y) +
      #((univ.image z ×ˢ univ) \ Z) < Fintype.card ι * Fintype.card W) :
    (triangles X Y Z).Nonempty := by
  have hsum := (add_le_add (add_le_add (sum_card_filter_notMem_le h.injective_left X)
    (sum_card_filter_notMem_le h.injective_middle Y))
    (sum_card_filter_notMem_le h.injective_right Z)).trans_lt hcard
  rw [← sum_add_distrib, ← sum_add_distrib] at hsum
  obtain ⟨i, -, hi⟩ := exists_lt_of_sum_lt (s := univ) (g := fun _ ↦ Fintype.card W)
    (by simpa using hsum)
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := exists_add_add_eq_zero_of_two_mul_card_lt
    (A := {a | (x i, a) ∈ X}) (B := {b | (y i, b) ∈ Y}) (C := {c | (z i, c) ∈ Z}) (by
      have := card_filter_add_card_filter_not (s := (univ : Finset W)) fun a ↦ (x i, a) ∈ X
      have := card_filter_add_card_filter_not (s := (univ : Finset W)) fun b ↦ (y i, b) ∈ Y
      have := card_filter_add_card_filter_not (s := (univ : Finset W)) fun c ↦ (z i, c) ∈ Z
      rw [card_univ] at *
      grind)
  simp only [mem_filter, mem_univ, true_and] at ha hb hc
  exact ⟨_, mem_triangles.2 ⟨ha, hb, hc, Prod.ext ((h i i i).2 ⟨rfl, rfl⟩) habc⟩⟩

end ArithmeticTriangleRemovalInVectorSpaces
