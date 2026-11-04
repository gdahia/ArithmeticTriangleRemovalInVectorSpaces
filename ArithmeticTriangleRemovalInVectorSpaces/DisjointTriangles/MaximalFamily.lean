/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.TensorPower

/-!
# Removing a maximum family of vertex-disjoint triangles

Let `S` be a family of vertex-disjoint triangles of `X × Y × Z` of maximum size. Removing the
vertices of `S` from `X`, `Y` and `Z` leaves no triangle, and costs at most `3 * #S` elements. By
Theorem 3 of Fox and Lovász, `X × Y × Z` contains at least `(#S / #V) ^ C p * #V ^ 2` triangles.
This proves Theorem 1 of Fox and Lovász in every finite vector space over `ZMod p`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.IsVertexDisjoint S`: no two triangles of `S` share a
  vertex.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.triangles_sdiff_image_eq_empty`: removing the vertices
  of a maximum family of vertex-disjoint triangles leaves no triangle.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_subset_card_sdiff_add_le_of_card_triangles_lt`:
  the arithmetic triangle removal lemma with `δ = (ε / 3) ^ C p`.
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {V : Type*}

/-- A family of triangles is vertex-disjoint if no two of its triangles share a first, second or
third vertex: each of the three projections is injective on it. -/
def IsVertexDisjoint (S : Finset (V × V × V)) : Prop :=
  Set.InjOn (fun ((x, _, _) : V × V × V) ↦ x) S ∧
    Set.InjOn (fun ((_, y, _) : V × V × V) ↦ y) S ∧ Set.InjOn (fun ((_, _, z) : V × V × V) ↦ z) S

/-- Removing the vertices of `S` from `X` removes at most `#S` elements. -/
lemma card_sdiff_sdiff_image_le {α : Type*} [DecidableEq α] (X : Finset α) (S : Finset (V × V × V))
    (f : V × V × V → α) : #(X \ (X \ S.image f)) ≤ #S := by
  rw [sdiff_sdiff_right_self]
  grw [card_le_card (inf_le_right : X ⊓ S.image f ≤ _), card_image_le]

variable [AddCommGroup V] [DecidableEq V] {X Y Z : Finset V} {S : Finset (V × V × V)}

/-- Removing the vertices of a maximum family `S` of vertex-disjoint triangles leaves no
triangle. -/
lemma triangles_sdiff_image_eq_empty (hST : S ⊆ triangles X Y Z) (hS : IsVertexDisjoint S)
    (hmax : ∀ S' ⊆ triangles X Y Z, IsVertexDisjoint S' → #S' ≤ #S) :
    triangles (X \ S.image fun (x, _, _) ↦ x) (Y \ S.image fun (_, y, _) ↦ y)
      (Z \ S.image fun (_, _, z) ↦ z) = ∅ := by
  refine eq_empty_of_forall_notMem ?_
  rintro ⟨x, y, z⟩ ht
  simp only [mem_triangles, mem_sdiff, mem_image] at ht
  obtain ⟨⟨hx, hxS⟩, ⟨hy, hyS⟩, ⟨hz, hzS⟩, hsum⟩ := ht
  have hnot : (x, y, z) ∉ S := fun h ↦ hxS ⟨_, h, rfl⟩
  have := hmax (insert (x, y, z) S)
    (insert_subset (mem_triangles.2 ⟨hx, hy, hz, hsum⟩) hST) ?_
  · rw [card_insert_of_notMem hnot] at this
    grind
  obtain ⟨h₁, h₂, h₃⟩ := hS
  rw [IsVertexDisjoint, coe_insert, Set.injOn_insert (by simpa using hnot),
    Set.injOn_insert (by simpa using hnot), Set.injOn_insert (by simpa using hnot)]
  exact ⟨⟨h₁, by simpa using hxS⟩, ⟨h₂, by simpa using hyS⟩, h₃, by simpa using hzS⟩

variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]

/-- **Theorem 3 for a family of triangles.** If `X × Y × Z` contains a family `S` of
vertex-disjoint triangles, then it contains at least `(#S / #V) ^ C p * #V ^ 2` triangles. -/
lemma div_rpow_C_mul_sq_le_card_triangles_of_isVertexDisjoint (hST : S ⊆ triangles X Y Z)
    (hS : IsVertexDisjoint S) :
    ((#S : ℝ) / Fintype.card V) ^ C p * Fintype.card V ^ 2 ≤ #(triangles X Y Z) := by
  obtain ⟨h₁, h₂, h₃⟩ := hS
  have := div_rpow_C_mul_sq_le_card_triangles (p := p) (X := X) (Y := Y) (Z := Z) h₁.injective
    h₂.injective h₃.injective ?_ ?_ ?_ ?_
  · simpa using this
  all_goals
    rintro ⟨⟨x, y, z⟩, ht⟩
    have := hST ht
    simp_all

/-- **Theorem 1 of Fox and Lovász** in a finite vector space `V` over `ZMod p`. If `X × Y × Z` has
fewer than `(ε / 3) ^ C p * #V ^ 2` triangles, then removing at most `ε * #V` elements from `X`, `Y`
and `Z` leaves no triangle. -/
theorem exists_subset_card_sdiff_add_le_of_card_triangles_lt {ε : ℝ} (hε : 0 ≤ ε)
    (h : #(triangles X Y Z) < (ε / 3) ^ C p * Fintype.card V ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z,
      #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * Fintype.card V ∧ triangles X' Y' Z' = ∅ := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_max_image ((triangles X Y Z).powerset.filter IsVertexDisjoint)
    card ⟨∅, by simp [IsVertexDisjoint]⟩
  rw [mem_filter, mem_powerset] at hS
  obtain ⟨hST, hS⟩ := hS
  refine ⟨_, sdiff_subset, _, sdiff_subset, _, sdiff_subset, ?_,
    triangles_sdiff_image_eq_empty hST hS fun S' hS' hdisj ↦ hmax S' (by simp [hS', hdisj])⟩
  have h3 : 3 * #S ≤ ε * Fintype.card V := by
    by_contra! hlt
    have hC : 0 ≤ C p := by
      have := c_pos (Fact.out : p.Prime).two_le
      rw [C]
      positivity
    have hεS : ε / 3 ≤ #S / Fintype.card V := by
      rw [div_le_div_iff₀ (by norm_num) (Nat.cast_pos.2 Fintype.card_pos)]
      linarith
    have := div_rpow_C_mul_sq_le_card_triangles_of_isVertexDisjoint (p := p) hST hS
    grw [← hεS] at this
    linarith
  linarith [(Nat.cast_le (α := ℝ)).2 (card_sdiff_sdiff_image_le X S fun (x, _, _) ↦ x),
    (Nat.cast_le (α := ℝ)).2 (card_sdiff_sdiff_image_le Y S fun (_, y, _) ↦ y),
    (Nat.cast_le (α := ℝ)).2 (card_sdiff_sdiff_image_le Z S fun (_, _, z) ↦ z)]

end ArithmeticTriangleRemovalInVectorSpaces
