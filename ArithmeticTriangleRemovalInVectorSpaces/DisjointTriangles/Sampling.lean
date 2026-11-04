/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import ArithmeticTriangleRemovalInVectorSpaces.LinearMap.Card
import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.TensorPower
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Few triangles when all degrees are small

This file proves Lemma 5 of Fox and Lovász: if every vertex of `X × Y × Z` lies in at most
`R = ρ * N` triangles, then there are at most `125 * p ^ 2 * ρ ^ (1 + c p) * N ^ 2` triangles. As in
the paper, the first two vertices of each triangle are linearly independent, and no plane contains
two triangles. The paper intersects `X`, `Y` and `Z` with a uniformly random subspace of dimension
`d`; we use the kernel of a uniformly random linear map `A : V →ₗ[ZMod p] W`. Its kernel contains
`r` given independent vectors with probability `#W ^ (-r)`, and the expected value of
`#(ker A) ^ (1 - c p)` is at most `(1 + #V / #W) ^ (1 - c p)` by Jensen's inequality.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.goodTriangles X Y Z`: the triangles of `X × Y × Z` that
  share no vertex with another triangle of `X × Y × Z`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_goodTriangles_le`: the good triangles of sets
  inside a subspace `U` form a multicolored sum-free family, so there are at most
  `Nat.card U ^ (1 - c p)` of them.
* `ArithmeticTriangleRemovalInVectorSpaces.two_mul_card_triangles_le`: the bound
  `2 * #(triangles X Y Z) ≤ 5 * #W ^ 2 * (1 + #V / #W) ^ (1 - c p)` when `5 * R ≤ #W`.
* `ArithmeticTriangleRemovalInVectorSpaces.card_triangles_le_of_degree_le`: Lemma 5 of Fox and
  Lovász.
-/

public section

open Finset Module Submodule

namespace ArithmeticTriangleRemovalInVectorSpaces

section Good

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The good triangles of Fox and Lovász: the triangles of `X × Y × Z` that share no vertex with
another triangle of `X × Y × Z`. -/
def goodTriangles (X Y Z : Finset G) : Finset (G × G × G) :=
  (triangles X Y Z).filter fun (x, y, z) ↦ ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z, x' + y' + z' = 0 →
    (x' = x ∨ y' = y ∨ z' = z) → x' = x ∧ y' = y ∧ z' = z

lemma goodTriangles_subset (X Y Z : Finset G) : goodTriangles X Y Z ⊆ triangles X Y Z :=
  filter_subset _ _

lemma mem_goodTriangles {X Y Z : Finset G} {x y z : G} :
    (x, y, z) ∈ goodTriangles X Y Z ↔ x ∈ X ∧ y ∈ Y ∧ z ∈ Z ∧ x + y + z = 0 ∧
      ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z, x' + y' + z' = 0 →
        (x' = x ∨ y' = y ∨ z' = z) → x' = x ∧ y' = y ∧ z' = z := by
  simp [goodTriangles, and_assoc]

end Good

variable {p : ℕ} [Fact p.Prime] {V W : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [AddCommGroup W] [Module (ZMod p) W] [Fintype W] [DecidableEq W]
  {X Y Z : Finset V}

omit [Fintype V] in
/-- The good triangles of sets inside a subspace `U` form a multicolored sum-free family in `U`,
so there are at most `Nat.card U ^ (1 - c p)` of them. -/
lemma card_goodTriangles_le [Finite V] (U : Submodule (ZMod p) V) (hX : ∀ x ∈ X, x ∈ U)
    (hY : ∀ y ∈ Y, y ∈ U) (hZ : ∀ z ∈ Z, z ∈ U) :
    (#(goodTriangles X Y Z) : ℝ) ≤ Nat.card U ^ (1 - c p) := by
  have := Fintype.ofFinite U
  have hmsf : IsMulticoloredSumFree
      (fun (⟨(x, _, _), ht⟩ : goodTriangles X Y Z) ↦
        (⟨x, hX x (by grind [mem_goodTriangles])⟩ : U))
      (fun ⟨(_, y, _), ht⟩ ↦ ⟨y, hY y (by grind [mem_goodTriangles])⟩)
      fun ⟨(_, _, z), ht⟩ ↦ ⟨z, hZ z (by grind [mem_goodTriangles])⟩ := by
    rintro ⟨⟨x, y, z⟩, hs⟩ ⟨⟨x', y', z'⟩, ht⟩ ⟨⟨x'', y'', z''⟩, hu⟩
    obtain ⟨hx, hy, hz, hsum, hgs⟩ := mem_goodTriangles.1 hs
    obtain ⟨-, hy', -, -, hgt⟩ := mem_goodTriangles.1 ht
    obtain ⟨-, -, hz'', -, hgu⟩ := mem_goodTriangles.1 hu
    simp only [Subtype.ext_iff, ZeroMemClass.coe_zero, Submodule.coe_add, Prod.ext_iff]
    refine ⟨?_, fun ⟨⟨h₁, h₂, h₃⟩, h₄, h₅, h₆⟩ ↦ by grind⟩
    intro h
    obtain ⟨-, hy₁, hz₁⟩ := hgs x hx y' hy' z'' hz'' h (Or.inl rfl)
    obtain ⟨hx₁, -, -⟩ := hgt x hx y hy z hz hsum (Or.inr (Or.inl hy₁.symm))
    obtain ⟨hx₂, -, -⟩ := hgu x hx y hy z hz hsum (Or.inr (Or.inr hz₁.symm))
    grind
  have := hmsf.card_le_card_rpow (p := p)
  rwa [Fintype.card_coe, ← Nat.card_eq_fintype_card] at this

/-- The arithmetic of Lemma 5 of Fox and Lovász: if `5 * ρ * N ≤ w ≤ 5 * p * ρ * N` and
`0 < ρ ≤ 1`, then `w ^ 2 * (1 + N / w) ^ (1 - c) ≤ 30 * p ^ 2 * ρ ^ (1 + c) * N ^ 2`. -/
lemma sq_mul_one_add_div_rpow_le {p ρ N w c : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hN : 0 < N)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hw₁ : 5 * (ρ * N) ≤ w) (hw₂ : w ≤ p * (5 * (ρ * N))) :
    w ^ 2 * (1 + N / w) ^ (1 - c) ≤ 30 * p ^ 2 * ρ ^ (1 + c) * N ^ 2 := by
  have hw : 0 < w := lt_of_lt_of_le (by positivity) hw₁
  calc w ^ 2 * (1 + N / w) ^ (1 - c)
      ≤ (p * (5 * (ρ * N))) ^ 2 * (6 / 5 / ρ) ^ (1 - c) := by
        gcongr
        grw [div_le_div_of_nonneg_left hN.le (by positivity) hw₁]
        field_simp
        linarith
    _ = 25 * p ^ 2 * N ^ 2 * (6 / 5) ^ (1 - c) * (ρ ^ 2 / ρ ^ (1 - c)) := by
        rw [Real.div_rpow (by norm_num) hρ₀.le]
        ring
    _ = 25 * p ^ 2 * N ^ 2 * (6 / 5) ^ (1 - c) * ρ ^ (1 + c) := by
        rw [← Real.rpow_two ρ, ← Real.rpow_sub hρ₀]
        ring_nf
    _ ≤ 25 * p ^ 2 * N ^ 2 * (6 / 5) * ρ ^ (1 + c) := by
        grw [Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
          (by linarith : 1 - c ≤ 1), Real.rpow_one]
    _ = 30 * p ^ 2 * ρ ^ (1 + c) * N ^ 2 := by ring

/-- **Jensen's inequality** for `t ↦ t ^ q` with `0 ≤ q ≤ 1`: a sum of `q`-th powers is at most the
number of terms times the `q`-th power of the mean. -/
lemma sum_rpow_le_card_mul_rpow {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∑ i ∈ s, f i ^ q ≤ #s * ((∑ i ∈ s, f i) / #s) ^ q := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hs' : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have := ConcaveOn.le_map_sum (Real.concaveOn_rpow hq₀ hq₁) (t := s)
    (w := fun _ ↦ (#s : ℝ)⁻¹) (p := f) (fun _ _ ↦ by positivity) (by simp [hs'.ne']) hf
  simp only [smul_eq_mul, ← mul_sum] at this
  rwa [inv_mul_le_iff₀ hs', ← div_eq_inv_mul] at this

section Count

variable [Fintype (V →ₗ[ZMod p] W)]

omit [Fintype V] [DecidableEq V] in
/-- The linear maps vanishing at linearly independent vectors `v 0, …, v (r - 1)` form a
proportion `#W ^ (-r)` of all linear maps. -/
lemma card_filter_forall_apply_eq_zero {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent (ZMod p) v) :
    (#{A : V →ₗ[ZMod p] W | ∀ i, A (v i) = 0} : ℝ) =
      Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ r := by
  have := hv.natCard_mul_pow_eq_natCard (K := ZMod p) (W := W)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card] at this
  rw [eq_div_iff (pow_pos (Nat.cast_pos.2 Fintype.card_pos) r).ne']
  exact_mod_cast this

omit [Fintype V] [DecidableEq V] in
/-- If `x` and `y` are linearly independent and `u` lies outside their span, then the linear maps
vanishing at `u`, `x` and `y` form a proportion `#W ^ (-3)` of all linear maps. -/
lemma card_filter_apply_eq_zero_of_notMem_span {u x y : V}
    (hli : LinearIndependent (ZMod p) ![x, y]) (hu : u ∉ span (ZMod p) {x, y}) :
    (#{A : V →ₗ[ZMod p] W | A u = 0 ∧ A x = 0 ∧ A y = 0} : ℝ) =
      Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 3 := by
  have hv : LinearIndependent (ZMod p) ![u, x, y] :=
    linearIndependent_finCons.2 ⟨hli, by rwa [Matrix.range_cons_cons_empty]⟩
  rw [← card_filter_forall_apply_eq_zero hv]
  congr 3 with A
  simp [Fin.forall_fin_succ]

omit [Fintype V] in
/-- A triangle `(x, y, z)` is good in the kernel of at least a proportion
`(1 - 3 * R / #W) / #W ^ 2` of the linear maps `A`: its first two vertices lie in the kernel with
probability `#W ^ (-2)`, and each of the at most `3 * R` triangles sharing a vertex with it lies in
the kernel as well with probability `#W ^ (-3)`. -/
lemma card_filter_mem_goodTriangles_ge {R : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ R)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ R)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ R) {x y z : V}
    (ht : (x, y, z) ∈ triangles X Y Z) :
    Fintype.card (V →ₗ[ZMod p] W) * (1 - 3 * R / Fintype.card W) / Fintype.card W ^ 2 ≤
      #{A : V →ₗ[ZMod p] W | (x, y, z) ∈
        goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} := by
  classical
  set N := (triangles X Y Z).filter fun (x', y', z') ↦ (x' = x ∨ y' = y ∨ z' = z) ∧
    ¬(x' = x ∧ y' = y)
  have hN : #N ≤ 3 * R := by
    have : N ⊆ ((triangles X Y Z).filter fun (x', _, _) ↦ x' = x) ∪
        ((triangles X Y Z).filter fun (_, y', _) ↦ y' = y) ∪
        (triangles X Y Z).filter fun (_, _, z') ↦ z' = z := by
      rintro ⟨x', y', z'⟩ h
      simp only [N, mem_filter, mem_union] at h ⊢
      tauto
    grw [card_le_card this, card_union_le, card_union_le]
    push_cast
    linarith [hX x, hY y, hZ z]
  have hsub : ({A : V →ₗ[ZMod p] W | ∀ i, A (![x, y] i) = 0} : Finset _) ⊆
      ({A : V →ₗ[ZMod p] W | (x, y, z) ∈
        goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} : Finset _) ∪
      N.biUnion fun (x', y', _) ↦
        {A : V →ₗ[ZMod p] W | A x = 0 ∧ A y = 0 ∧ A x' = 0 ∧ A y' = 0} := by
    intro A hA
    simp only [mem_filter, mem_univ, true_and, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at hA
    obtain ⟨hAx, hAy⟩ := hA
    obtain ⟨hx, hy, hz, hsum⟩ := mem_triangles.1 ht
    have hAz : A z = 0 := by
      rw [eq_neg_of_add_eq_zero_right hsum, map_neg, map_add, hAx, hAy, add_zero, neg_zero]
    by_contra hcon
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_biUnion, not_or, not_exists,
      not_and] at hcon
    obtain ⟨hgood, hN'⟩ := hcon
    refine hgood (mem_goodTriangles.2 ⟨mem_filter.2 ⟨hx, hAx⟩, mem_filter.2 ⟨hy, hAy⟩,
      mem_filter.2 ⟨hz, hAz⟩, hsum, ?_⟩)
    intro x' hx' y' hy' z' hz' hsum' hshare
    obtain ⟨hx', hAx'⟩ := mem_filter.1 hx'
    obtain ⟨hy', hAy'⟩ := mem_filter.1 hy'
    obtain ⟨hz', -⟩ := mem_filter.1 hz'
    by_cases hxy : x' = x ∧ y' = y
    · grind
    · exact (hN' (x', y', z') (mem_filter.2 ⟨mem_triangles.2 ⟨hx', hy', hz', hsum'⟩, hshare, hxy⟩)
        hAx hAy hAx' hAy').elim
  have htriple {x' y' z' : V} (ht' : (x', y', z') ∈ N) :
      (#({A : V →ₗ[ZMod p] W | A x = 0 ∧ A y = 0 ∧ A x' = 0 ∧ A y' = 0} : Finset _) : ℝ) ≤
        Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 3 := by
    obtain ⟨ht', -, hxy⟩ := mem_filter.1 ht'
    by_cases hx' : x' ∈ span (ZMod p) {x, y}
    · rw [← card_filter_apply_eq_zero_of_notMem_span (hli x y z ht)
        fun hy' ↦ hxy (hspan x y z ht x' y' z' ht' hx' hy')]
      exact_mod_cast card_le_card (monotone_filter_right _ fun A ↦ by tauto)
    · rw [← card_filter_apply_eq_zero_of_notMem_span (hli x y z ht) hx']
      exact_mod_cast card_le_card (monotone_filter_right _ fun A ↦ by tauto)
  have hcard := card_le_card hsub
  grw [card_union_le, card_biUnion_le] at hcard
  have hw : (Fintype.card W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_le (α := ℝ)] at hcard
  push_cast at hcard
  grw [sum_le_card_nsmul _ _ _ fun ⟨x', y', z'⟩ ht' ↦ htriple ht', nsmul_eq_mul, hN,
    card_filter_forall_apply_eq_zero (hli x y z ht)] at hcard
  linarith [(by field_simp : (Fintype.card (V →ₗ[ZMod p] W) : ℝ) *
    (1 - 3 * R / Fintype.card W) / Fintype.card W ^ 2 = Fintype.card (V →ₗ[ZMod p] W) /
      Fintype.card W ^ 2 - 3 * R * (Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 3))]

omit [DecidableEq V] in
/-- The kernels of the linear maps `A : V →ₗ[ZMod p] W` have at most
`#(V →ₗ[ZMod p] W) * (1 + #V / #W)` elements in total: each nonzero vector lies in a proportion
`1 / #W` of the kernels. -/
lemma sum_card_ker_le :
    ∑ A : V →ₗ[ZMod p] W, (#{v | A v = 0} : ℝ) ≤
      Fintype.card (V →ₗ[ZMod p] W) * (1 + Fintype.card V / Fintype.card W) := by
  classical
  have hterm (v : V) : (#{A : V →ₗ[ZMod p] W | A v = 0} : ℝ) ≤
      (if v = 0 then (Fintype.card (V →ₗ[ZMod p] W) : ℝ) else 0) +
        Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W := by
    by_cases hv : v = 0
    · simp [hv, div_nonneg]
    · have := card_filter_forall_apply_eq_zero (W := W)
        (linearIndependent_unique_iff.2 (by simpa using hv) : LinearIndependent (ZMod p) ![v])
      simp_all
  have hswap : ∑ A : V →ₗ[ZMod p] W, #{v | A v = 0} = ∑ v, #{A : V →ₗ[ZMod p] W | A v = 0} :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
  rw [← Nat.cast_sum, hswap, Nat.cast_sum]
  grw [sum_le_sum fun v _ ↦ hterm v, sum_add_distrib]
  simp
  ring_nf
  rfl

/-- Summing the bound of `card_goodTriangles_le` over the kernels of all linear maps `A`, with
Jensen's inequality for the average size of the kernels. -/
lemma sum_card_goodTriangles_le :
    ∑ A : V →ₗ[ZMod p] W,
      (#(goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))) : ℝ) ≤
      Fintype.card (V →ₗ[ZMod p] W) * (1 + Fintype.card V / Fintype.card W) ^ (1 - c p) := by
  have hp := (Fact.out : p.Prime).two_le
  have hc : 0 ≤ 1 - c p := by linarith [c_lt_one hp]
  have hker (A : V →ₗ[ZMod p] W) : Nat.card (LinearMap.ker A) = #{v | A v = 0} := by
    simp [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  grw [sum_le_sum fun A _ ↦ card_goodTriangles_le (LinearMap.ker A)
    (fun x hx ↦ LinearMap.mem_ker.2 (mem_filter.1 hx).2)
    (fun y hy ↦ LinearMap.mem_ker.2 (mem_filter.1 hy).2)
    (fun z hz ↦ LinearMap.mem_ker.2 (mem_filter.1 hz).2)]
  simp only [hker]
  grw [sum_rpow_le_card_mul_rpow _ (fun _ _ ↦ by positivity) hc (by linarith [c_pos hp]),
    card_univ, sum_card_ker_le, mul_div_cancel_left₀ _ (Nat.cast_pos.2 Fintype.card_pos).ne']
  exact div_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [DecidableEq W] [Fintype (V →ₗ[ZMod p] W)] in
/-- Double counting the pairs `(t, A)` such that the triangle `t` is good in the kernel of `A`. -/
lemma card_triangles_mul_le {R : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ R)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ R)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ R) :
    #(triangles X Y Z) * (1 - 3 * R / Fintype.card W) ≤
      Fintype.card W ^ 2 * (1 + Fintype.card V / Fintype.card W) ^ (1 - c p) := by
  classical
  have := Fintype.ofFinite (V →ₗ[ZMod p] W)
  have hcount := card_nsmul_le_sum (triangles X Y Z) (fun t ↦ (#{A : V →ₗ[ZMod p] W |
    t ∈ goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} : ℝ)) _
    fun ⟨x, y, z⟩ ht ↦ card_filter_mem_goodTriangles_ge hli hspan hX hY hZ ht
  have hdouble : ∑ t ∈ triangles X Y Z, #{A : V →ₗ[ZMod p] W |
      t ∈ goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))} ≤
      ∑ A : V →ₗ[ZMod p] W,
        #(goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0))) := by
    refine (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun t (A : V →ₗ[ZMod p] W) ↦
        t ∈ goodTriangles (X.filter (A · = 0)) (Y.filter (A · = 0)) (Z.filter (A · = 0)))).trans_le
      ?_
    gcongr with A
    intro t ht
    obtain ⟨-, ht⟩ := mem_filter.1 ht
    exact ht
  rw [← Nat.cast_le (α := ℝ)] at hdouble
  push_cast at hdouble
  simp only [nsmul_eq_mul] at hcount
  rw [← mul_le_mul_iff_of_pos_left (div_pos (Nat.cast_pos.2 Fintype.card_pos)
    (pow_pos (Nat.cast_pos.2 Fintype.card_pos) 2) :
    (0 : ℝ) < Fintype.card (V →ₗ[ZMod p] W) / Fintype.card W ^ 2)]
  convert hcount.trans (hdouble.trans sum_card_goodTriangles_le) using 1 <;> field_simp

omit [DecidableEq W] [Fintype (V →ₗ[ZMod p] W)] in
/-- If every vertex lies in at most `R` triangles and `5 * R ≤ #W`, then
`2 * #(triangles X Y Z) ≤ 5 * #W ^ 2 * (1 + #V / #W) ^ (1 - c p)`. -/
lemma two_mul_card_triangles_le {R : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ R)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ R)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ R)
    (hR : 5 * R ≤ Fintype.card W) :
    (2 : ℝ) * #(triangles X Y Z) ≤
      5 * Fintype.card W ^ 2 * (1 + Fintype.card V / Fintype.card W) ^ (1 - c p) := by
  have hw : (0 : ℝ) < Fintype.card W := Nat.cast_pos.2 Fintype.card_pos
  have := card_triangles_mul_le (W := W) hli hspan hX hY hZ
  grw [← (by rw [le_sub_comm, div_le_iff₀ hw]; linarith : (2 / 5 : ℝ) ≤
    1 - 3 * R / Fintype.card W)] at this
  linarith

end Count

/-- **Lemma 5 of Fox and Lovász.** Let `X`, `Y` and `Z` be sets in a finite vector space `V` over
`ZMod p` such that the first two vertices of each triangle are linearly independent and their span
contains the first two vertices of no other triangle. If every vertex lies in at most `ρ * #V`
triangles, then there are at most `125 * p ^ 2 * ρ ^ (1 + c p) * #V ^ 2` triangles. -/
lemma card_triangles_le_of_degree_le {ρ : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ ρ * Fintype.card V)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ ρ * Fintype.card V)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ ρ * Fintype.card V) :
    #(triangles X Y Z) ≤ 125 * p ^ 2 * ρ ^ (1 + c p) * Fintype.card V ^ 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  obtain hT | ⟨⟨x, y, z⟩, ht⟩ := (triangles X Y Z).eq_empty_or_nonempty
  · have : 0 ≤ ρ := nonneg_of_mul_nonneg_left ((Nat.cast_nonneg _).trans (hX 0)) hN
    simp only [hT, card_empty, Nat.cast_zero]
    positivity
  have hρN : 1 ≤ ρ * Fintype.card V :=
    (hX x).trans' (Nat.one_le_cast.2 (card_pos.2 ⟨_, mem_filter.2 ⟨ht, rfl⟩⟩))
  have hρ₀ : 0 < ρ := pos_of_mul_pos_left (one_pos.trans_le hρN) hN.le
  obtain hρ | hρ := le_or_gt 1 ρ
  · grw [card_triangles_le_card_sq]
    push_cast
    exact le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le (by nlinarith)
      (Real.one_le_rpow hρ (by linarith [c_pos (p := p) (by exact_mod_cast hp)])))
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near (by linarith : 1 ≤ 5 * (ρ * Fintype.card V))
    (by linarith : (1 : ℝ) < p)
  have h2 := two_mul_card_triangles_le (W := Fin (n + 1) → ZMod p) hli hspan hX hY hZ
    (by simpa using hn₂.le)
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow] at h2
  linarith [sq_mul_one_add_div_rpow_le hρ₀ hρ.le hN (c_pos (p := p) (by exact_mod_cast hp)).le
    (c_lt_one (p := p) (by exact_mod_cast hp)).le hn₂.le (by rw [pow_succ']; gcongr),
    (by positivity : 0 ≤ (p : ℝ) ^ 2 * ρ ^ (1 + c p) * Fintype.card V ^ 2)]

end ArithmeticTriangleRemovalInVectorSpaces
