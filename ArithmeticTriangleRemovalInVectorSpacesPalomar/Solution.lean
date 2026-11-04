/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module -- shake: keep-all

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import ArithmeticTriangleRemovalInVectorSpaces.Construction.LowerBound
import ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.MaximalFamily
import ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.TensorPower
import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.SmallPrimes
import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.TensorPower
import ArithmeticTriangleRemovalInVectorSpaces.ZMod

/-!
# A tight bound for Green's arithmetic triangle removal lemma in vector spaces

The statements of `Challenge.lean`, which are the results of the library with the same names
without the primes. The definitions `triangles`, `IsMulticoloredSumFree`, `c` and `C` are those of
the library.
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {p : ℕ} [Fact p.Prime]

section VectorSpace

variable {V ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V] [Fintype ι]

/-- **The Kleinberg–Sawin–Speyer bound** (Theorem 2 of Fox and Lovász) in a finite vector space
`V` over `ZMod p`. A multicolored sum-free family in `V` has at most `#V ^ (1 - c p)` members. -/
theorem IsMulticoloredSumFree.card_le_card_rpow' {x y z : ι → V}
    (h : IsMulticoloredSumFree x y z) :
    (Fintype.card ι : ℝ) ≤ Fintype.card V ^ (1 - c p) :=
  h.card_le_card_rpow

variable [DecidableEq V]

/-- **Theorem 3 of Fox and Lovász** in a finite vector space `V` over `ZMod p`. If `X × Y × Z`
contains `m` vertex-disjoint triangles `(x i, y i, z i)`, then it contains at least
`(m / #V) ^ C p * #V ^ 2` triangles. -/
theorem div_rpow_C_mul_sq_le_card_triangles' {x y z : ι → V} {X Y Z : Finset V}
    (hx : Injective x) (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X)
    (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    ((Fintype.card ι : ℝ) / Fintype.card V) ^ C p * Fintype.card V ^ 2 ≤ #(triangles X Y Z) :=
  div_rpow_C_mul_sq_le_card_triangles hx hy hz hxX hyY hzZ hsum

/-- **Theorem 1 of Fox and Lovász** in a finite vector space `V` over `ZMod p`. If `X × Y × Z` has
fewer than `(ε / 3) ^ C p * #V ^ 2` triangles, then removing at most `ε * #V` elements from `X`, `Y`
and `Z` leaves no triangle. -/
theorem exists_subset_card_sdiff_add_le_of_card_triangles_lt' {ε : ℝ} (hε : 0 ≤ ε)
    {X Y Z : Finset V} (h : #(triangles X Y Z) < (ε / 3) ^ C p * Fintype.card V ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z,
      #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * Fintype.card V ∧ triangles X' Y' Z' = ∅ :=
  exists_subset_card_sdiff_add_le_of_card_triangles_lt hε h

end VectorSpace

variable {n : ℕ}

/-- **The Kleinberg–Sawin–Speyer bound** (Theorem 2 of Fox and Lovász). A multicolored sum-free
family in `Fin n → ZMod p` has at most `p ^ ((1 - c p) * n)` members. -/
theorem IsMulticoloredSumFree.card_le_rpow_mul' {ι : Type*} [Fintype ι]
    {x y z : ι → Fin n → ZMod p} (h : IsMulticoloredSumFree x y z) :
    Fintype.card ι ≤ (p : ℝ) ^ ((1 - c p) * n) :=
  h.card_le_rpow_mul

/-- **Theorem 3 of Fox and Lovász.** If `X × Y × Z` contains `m` vertex-disjoint triangles
`(x i, y i, z i)` in `Fin n → ZMod p`, then it contains at least `(m / N) ^ C p * N ^ 2` triangles,
where `N = p ^ n`. -/
theorem div_pow_rpow_C_mul_sq_le_card_triangles' {ι : Type*} [Fintype ι]
    {x y z : ι → Fin n → ZMod p} {X Y Z : Finset (Fin n → ZMod p)} (hx : Injective x)
    (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y)
    (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι / (p : ℝ) ^ n) ^ C p * ((p : ℝ) ^ n) ^ 2 ≤ #(triangles X Y Z) :=
  div_pow_rpow_C_mul_sq_le_card_triangles hx hy hz hxX hyY hzZ hsum

/-- **Theorem 1 of Fox and Lovász: the arithmetic triangle removal lemma.** If `X × Y × Z` has
fewer than `(ε / 3) ^ C p * N ^ 2` triangles in `Fin n → ZMod p`, where `N = p ^ n`, then removing
at most `ε * N` elements from `X`, `Y` and `Z` leaves no triangle. -/
theorem exists_subset_card_sdiff_add_le_triangles_eq_empty' {ε : ℝ} (hε : 0 ≤ ε)
    {X Y Z : Finset (Fin n → ZMod p)}
    (h : #(triangles X Y Z) < (ε / 3) ^ C p * ((p : ℝ) ^ n) ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z,
      #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧ triangles X' Y' Z' = ∅ :=
  exists_subset_card_sdiff_add_le_triangles_eq_empty hε h

variable {l : ℕ} {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}

/-- **The construction of Section 3 of Fox and Lovász, part one.** For a multicolored sum-free
family of `m` triples in `Fin n → ZMod p` with vertex sets `X`, `Y` and `Z`, the sets `X × W`,
`Y × W` and `Z × W` with `W = Fin l → ZMod p` contain `m * p ^ (2 * l)` triangles. -/
theorem IsMulticoloredSumFree.card_triangles_prod_pi' (h : IsMulticoloredSumFree x y z) :
    #(triangles (univ.image x ×ˢ (univ : Finset (Fin l → ZMod p))) (univ.image y ×ˢ univ)
      (univ.image z ×ˢ univ)) = Fintype.card ι * p ^ (2 * l) :=
  h.card_triangles_prod_pi

/-- **The construction of Section 3 of Fox and Lovász, part two.** Removing fewer than
`m * p ^ l` elements from the sets `X × W`, `Y × W` and `Z × W` of
`card_triangles_prod_pi'` leaves a triangle. -/
theorem IsMulticoloredSumFree.triangles_prod_pi_nonempty' (h : IsMulticoloredSumFree x y z)
    {X' Y' Z' : Finset ((Fin n → ZMod p) × (Fin l → ZMod p))}
    (hcard : #((univ.image x ×ˢ univ) \ X') + #((univ.image y ×ˢ univ) \ Y') +
      #((univ.image z ×ˢ univ) \ Z') < Fintype.card ι * p ^ l) :
    (triangles X' Y' Z').Nonempty :=
  h.triangles_prod_pi_nonempty hcard

omit [Fact p.Prime] in
/-- **Tightness of the arithmetic triangle removal lemma** (Section 3 of Fox and Lovász). Suppose
that in `Fin n → ZMod p` every `X × Y × Z` with fewer than `δ * N ^ 2` triangles can be made
triangle-free by removing at most `ε * N` elements, where `N = p ^ n`. Then every multicolored
sum-free family of more than `ε * N` triples has at least `δ * N ^ 2` members. -/
theorem IsMulticoloredSumFree.mul_sq_le_card_of_forall_exists_subset' {ε δ : ℝ}
    (h : IsMulticoloredSumFree x y z) (hε : ε * p ^ n < Fintype.card ι)
    (hδ : ∀ X Y Z : Finset (Fin n → ZMod p), #(triangles X Y Z) < δ * ((p : ℝ) ^ n) ^ 2 →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z,
        #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧ triangles X' Y' Z' = ∅) :
    δ * ((p : ℝ) ^ n) ^ 2 ≤ Fintype.card ι :=
  h.mul_sq_le_card_of_forall_exists_subset hε hδ

omit [Fact p.Prime] in
/-- **Large multicolored sum-free families** (Kleinberg, Sawin and Speyer, using Pebody's theorem;
the second part of Theorem 2 of Fox and Lovász). For `p ≥ 2` and `η > 0`, every large `n` has a
multicolored sum-free family in `Fin n → ZMod p` with at least `p ^ ((1 - c p - η) * n)`
members. -/
theorem exists_forall_ge_exists_isMulticoloredSumFree' (hp : 2 ≤ p) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p),
      IsMulticoloredSumFree x y z ∧ (p : ℝ) ^ ((1 - c p - η) * n) ≤ m :=
  exists_forall_ge_exists_isMulticoloredSumFree hp hη

/-- **Asymptotic tightness of the arithmetic triangle removal lemma** (the "Furthermore" part of
Theorem 1 of Fox and Lovász). For every `η > 0` and every small `ε > 0`, any `δ` that works with
`ε` in the removal lemma in `Fin n → ZMod p` for every `n` satisfies `δ ≤ ε ^ (C p - η)`. -/
theorem exists_pos_forall_le_rpow_C_sub' {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ δ : ℝ,
      (∀ n (X Y Z : Finset (Fin n → ZMod p)), #(triangles X Y Z) < δ * ((p : ℝ) ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z,
          #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧ triangles X' Y' Z' = ∅) →
      δ ≤ ε ^ (C p - η) :=
  exists_pos_forall_le_rpow_C_sub hη

/-- **The exponent `c_2`.** `c 2 = 5 / 3 - logb 2 3`. -/
theorem c_two' : c 2 = 5 / 3 - Real.logb 2 3 :=
  c_two

/-- **The exponent `c_3`.** With `a = (√33 - 1) / 8` and
`b = a ^ (-2 / 3) + a ^ (1 / 3) + a ^ (4 / 3)`, `c 3 = 1 - log b / log 3`. -/
theorem c_three' {a : ℝ} (ha : a = (√33 - 1) / 8) :
    c 3 = 1 - Real.log (a ^ (-2 / 3 : ℝ) + a ^ (1 / 3 : ℝ) + a ^ (4 / 3 : ℝ)) / Real.log 3 :=
  c_three ha

end ArithmeticTriangleRemovalInVectorSpaces
