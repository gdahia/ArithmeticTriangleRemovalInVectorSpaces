/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.Construction.TypeClass
public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
import ArithmeticTriangleRemovalInVectorSpaces.Construction.Behrend
import ArithmeticTriangleRemovalInVectorSpaces.Construction.Hash
import Mathlib.NumberTheory.Bertrand

/-!
# The sum-free family of a base point

Let `f₀ : Fin n → ℕ × ℕ × ℕ` be a sequence of triples summing to `p - 1`. The triples `(a, b, c)`
of vectors summing to `p - 1`, with `a`, `b` and `c` in the type classes of the three coordinates
of `f₀`, are permuted transitively in each coordinate, so each vector lies in equally many of
them. Hashing them with a prime `P` chosen by Bertrand's postulate into a set chosen by Behrend's
construction gives a multicolored sum-free family nearly as large as the smallest type class.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.baseTriples p f₀`: the triples of the type classes of
  the coordinates of `f₀` summing to `p - 1`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_typeClass`: a
  multicolored sum-free family in `Fin n → ZMod p` with at least
  `w exp (-4 √(log ((36 + 2 p) p ^ (3 n)))) / (4 (36 + 2 p))` members, where `w` is at most the
  size of each type class.
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n p : ℕ}

/-- Permuting the entries of the three vectors of a triple simultaneously. -/
@[expose] def permTriple (σ : Equiv.Perm (Fin n)) (v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :
    (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) :=
  (v.1 ∘ σ, v.2.1 ∘ σ, v.2.2 ∘ σ)

lemma permTriple_permTriple (σ τ : Equiv.Perm (Fin n))
    (v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :
    permTriple σ (permTriple τ v) = permTriple (τ * σ) v :=
  rfl

lemma permTriple_one (v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) : permTriple 1 v = v :=
  rfl

lemma comp_mem_typeClass {a b : Fin n → ℕ} (hb : b ∈ typeClass a) (σ : Equiv.Perm (Fin n)) :
    b ∘ σ ∈ typeClass a := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  exact mem_typeClass.2 ⟨τ * σ, rfl⟩

lemma exists_eq_comp_of_mem_typeClass {a b b' : Fin n → ℕ} (hb : b ∈ typeClass a)
    (hb' : b' ∈ typeClass a) : ∃ σ : Equiv.Perm (Fin n), b' = b ∘ σ := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  obtain ⟨τ', rfl⟩ := mem_typeClass.1 hb'
  refine ⟨τ⁻¹ * τ', ?_⟩
  ext r
  simp

lemma sum_eq_of_mem_typeClass {a b : Fin n → ℕ} (hb : b ∈ typeClass a) :
    ∑ r, b r = ∑ r, a r := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  exact Equiv.sum_comp τ a

lemma card_typeClass_le {a : Fin n → ℕ} (ha : ∀ r, a r < p) : #(typeClass a) ≤ p ^ n := by
  have hsub : typeClass a ⊆ Fintype.piFinset fun _ ↦ range p := by
    intro b hb
    obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
    simp [ha]
  grw [card_le_card hsub]
  simp

/-- The triples `(a, b, c)` summing to `p - 1` with `a`, `b` and `c` in the type classes of the
three coordinates of `f₀`. -/
def baseTriples (p : ℕ) (f₀ : Fin n → ℕ × ℕ × ℕ) :
    Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :=
  {v ∈ typeClass (fun r ↦ (f₀ r).1) ×ˢ typeClass (fun r ↦ (f₀ r).2.1) ×ˢ
    typeClass (fun r ↦ (f₀ r).2.2) | ∀ r, v.1 r + v.2.1 r + v.2.2 r = p - 1}

variable {f₀ : Fin n → ℕ × ℕ × ℕ}

lemma card_baseTriples_le (hp : 2 ≤ p) (hf₀ : ∀ r, (f₀ r).1 + (f₀ r).2.1 + (f₀ r).2.2 = p - 1) :
    #(baseTriples p f₀) ≤ p ^ (3 * n) := by
  rw [baseTriples]
  grw [card_filter_le, card_product, card_product,
    card_typeClass_le (p := p) (fun r ↦ by grind [hf₀ r]),
    card_typeClass_le (p := p) (fun r ↦ by grind [hf₀ r]),
    card_typeClass_le (p := p) (fun r ↦ by grind [hf₀ r])]
  exact le_of_eq (by ring)

lemma mem_baseTriples {v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} :
    v ∈ baseTriples p f₀ ↔ (v.1 ∈ typeClass (fun r ↦ (f₀ r).1) ∧
      v.2.1 ∈ typeClass (fun r ↦ (f₀ r).2.1) ∧ v.2.2 ∈ typeClass (fun r ↦ (f₀ r).2.2)) ∧
      ∀ r, v.1 r + v.2.1 r + v.2.2 r = p - 1 := by
  simp [baseTriples]

lemma permTriple_mem_baseTriples {v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)}
    (hv : v ∈ baseTriples p f₀) (σ : Equiv.Perm (Fin n)) : permTriple σ v ∈ baseTriples p f₀ := by
  obtain ⟨⟨h₁, h₂, h₃⟩, hsum⟩ := mem_baseTriples.1 hv
  exact mem_baseTriples.2 ⟨⟨comp_mem_typeClass h₁ σ, comp_mem_typeClass h₂ σ,
    comp_mem_typeClass h₃ σ⟩, fun r ↦ hsum (σ r)⟩

/-- **Equal fibers.** If permutations act on `V` compatibly with a projection `g` onto a set `W` on
which they act transitively, then every fiber of `g` has `|V| / |W|` elements. -/
lemma card_filter_mul_card_eq {V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))}
    {W : Finset (Fin n → ℕ)} (g : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → Fin n → ℕ)
    (hg : ∀ σ v, g (permTriple σ v) = g v ∘ σ) (hgW : ∀ v ∈ V, g v ∈ W)
    (hW : ∀ w ∈ W, ∀ w' ∈ W, ∃ σ : Equiv.Perm (Fin n), w' = w ∘ σ)
    (hV : ∀ σ, ∀ v ∈ V, permTriple σ v ∈ V) {v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)}
    (hv : v ∈ V) : #{v' ∈ V | g v = g v'} * #W = #V := by
  rw [card_eq_sum_card_fiberwise hgW, sum_const_nat, mul_comm]
  intro w hw
  obtain ⟨σ, rfl⟩ := hW (g v) (hgW v hv) w hw
  symm
  refine card_nbij' (permTriple σ) (permTriple σ⁻¹) ?_ ?_ ?_ ?_
  · intro v' hv'
    simp only [coe_filter, Set.mem_ofPred_eq] at hv' ⊢
    obtain ⟨hv'V, hv'g⟩ := hv'
    exact ⟨hV σ v' hv'V, by rw [hg, hv'g]⟩
  · intro v' hv'
    simp only [coe_filter, Set.mem_ofPred_eq] at hv' ⊢
    obtain ⟨hv'V, hv'g⟩ := hv'
    refine ⟨hV σ⁻¹ v' hv'V, ?_⟩
    rw [hg, hv'g]
    ext r
    simp
  · intro v' _
    rw [permTriple_permTriple, mul_inv_cancel, permTriple_one]
  · intro v' _
    rw [permTriple_permTriple, inv_mul_cancel, permTriple_one]

/-- **The sum-free family of a base point.** If `f₀` is a sequence of triples summing to `p - 1`
and `1 ≤ w` is at most the size of each type class of a coordinate of `f₀`, then there is a
multicolored sum-free family in `Fin n → ZMod p` with at least
`w exp (-4 √(log ((36 + 2 p) p ^ (3 n)))) / (4 (36 + 2 p))` members. -/
lemma exists_isMulticoloredSumFree_of_typeClass (hp : 2 ≤ p)
    (hf₀ : ∀ r, (f₀ r).1 + (f₀ r).2.1 + (f₀ r).2.2 = p - 1) {w : ℝ} (hw : 1 ≤ w)
    (hw₁ : w ≤ #(typeClass fun r ↦ (f₀ r).1)) (hw₂ : w ≤ #(typeClass fun r ↦ (f₀ r).2.1))
    (hw₃ : w ≤ #(typeClass fun r ↦ (f₀ r).2.2)) :
    ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p), IsMulticoloredSumFree x y z ∧
      w * exp (-4 * √(log ((36 + 2 * p) * p ^ (3 * n)))) / (4 * (36 + 2 * p)) ≤ m := by
  set V := baseTriples p f₀
  set W₁ := typeClass fun r ↦ (f₀ r).1
  set W₂ := typeClass fun r ↦ (f₀ r).2.1
  set W₃ := typeClass fun r ↦ (f₀ r).2.2
  have hv₀ : ((fun r ↦ (f₀ r).1), (fun r ↦ (f₀ r).2.1), fun r ↦ (f₀ r).2.2) ∈ V :=
    mem_baseTriples.2 ⟨⟨mem_typeClass.2 ⟨1, rfl⟩, mem_typeClass.2 ⟨1, rfl⟩,
      mem_typeClass.2 ⟨1, rfl⟩⟩, hf₀⟩
  have hV (v) (hv : v ∈ V) : ∀ r, v.1 r + v.2.1 r + v.2.2 r = p - 1 := (mem_baseTriples.1 hv).2
  have hclosed : ∀ v ∈ V, ∀ v' ∈ V, ∀ v'' ∈ V, (∀ r, v.1 r + v'.2.1 r + v''.2.2 r = p - 1) →
      (v.1, v'.2.1, v''.2.2) ∈ V := by
    intro v hv v' hv' v'' hv'' h
    obtain ⟨⟨h₁, -, -⟩, -⟩ := mem_baseTriples.1 hv
    obtain ⟨⟨-, h₂, -⟩, -⟩ := mem_baseTriples.1 hv'
    obtain ⟨⟨-, -, h₃⟩, -⟩ := mem_baseTriples.1 hv''
    exact mem_baseTriples.2 ⟨⟨h₁, h₂, h₃⟩, h⟩
  have hsum : ∀ v ∈ V, ∀ v' ∈ V, ∀ v'' ∈ V, ∑ r, (v.1 r + v'.2.1 r + v''.2.2 r) = n * (p - 1) := by
    intro v hv v' hv' v'' hv''
    obtain ⟨⟨h₁, -, -⟩, -⟩ := mem_baseTriples.1 hv
    obtain ⟨⟨-, h₂, -⟩, -⟩ := mem_baseTriples.1 hv'
    obtain ⟨⟨-, -, h₃⟩, -⟩ := mem_baseTriples.1 hv''
    rw [sum_add_distrib, sum_add_distrib, sum_eq_of_mem_typeClass h₁, sum_eq_of_mem_typeClass h₂,
      sum_eq_of_mem_typeClass h₃, ← sum_add_distrib, ← sum_add_distrib]
    simp [hf₀]
  have hperm := fun σ v (hv : v ∈ V) ↦ permTriple_mem_baseTriples hv σ
  have hfib₁ (v) (hv : v ∈ V) : #{v' ∈ V | v.1 = v'.1} * #W₁ = #V :=
    card_filter_mul_card_eq (fun v ↦ v.1) (fun _ _ ↦ rfl) (fun v hv ↦ (mem_baseTriples.1 hv).1.1)
      (fun _ h _ h' ↦ exists_eq_comp_of_mem_typeClass h h') hperm hv
  have hfib₂ (v) (hv : v ∈ V) : #{v' ∈ V | v.2.1 = v'.2.1} * #W₂ = #V :=
    card_filter_mul_card_eq (fun v ↦ v.2.1) (fun _ _ ↦ rfl)
      (fun v hv ↦ (mem_baseTriples.1 hv).1.2.1)
      (fun _ h _ h' ↦ exists_eq_comp_of_mem_typeClass h h') hperm hv
  have hfib₃ (v) (hv : v ∈ V) : #{v' ∈ V | v.2.2 = v'.2.2} * #W₃ = #V :=
    card_filter_mul_card_eq (fun v ↦ v.2.2) (fun _ _ ↦ rfl)
      (fun v hv ↦ (mem_baseTriples.1 hv).1.2.2)
      (fun _ h _ h' ↦ exists_eq_comp_of_mem_typeClass h h') hperm hv
  have hW₁ : 0 < #W₁ := card_pos.2 ⟨_, mem_typeClass.2 ⟨1, rfl⟩⟩
  have hW₂ : 0 < #W₂ := card_pos.2 ⟨_, mem_typeClass.2 ⟨1, rfl⟩⟩
  have hW₃ : 0 < #W₃ := card_pos.2 ⟨_, mem_typeClass.2 ⟨1, rfl⟩⟩
  set F := #V / #W₁ + #V / #W₂ + #V / #W₃
  have hF (v) (hv : v ∈ V) : #{v' ∈ V | v.1 = v'.1} ≤ F ∧ #{v' ∈ V | v.2.1 = v'.2.1} ≤ F ∧
      #{v' ∈ V | v.2.2 = v'.2.2} ≤ F := by
    have h₁ := Nat.eq_div_of_mul_eq_left hW₁.ne' (hfib₁ v hv)
    have h₂ := Nat.eq_div_of_mul_eq_left hW₂.ne' (hfib₂ v hv)
    have h₃ := Nat.eq_div_of_mul_eq_left hW₃.ne' (hfib₃ v hv)
    grind
  obtain ⟨P, hPprime, hPlt, hPle⟩ := Nat.exists_prime_lt_and_le_two_mul (6 * F + p) (by grind)
  have := Fact.mk hPprime
  obtain ⟨S, hS, hScard⟩ := exists_finset_zmod_add_eq_add_lower_bound hPprime.pos
  obtain ⟨m, x, y, z, hsf, hm⟩ := exists_isMulticoloredSumFree_of_hash (V := V) (S := S) hp
    (by grind) hV hclosed hsum (fun v hv ↦ (hF v hv).1) (fun v hv ↦ (hF v hv).2.1)
    (fun v hv ↦ (hF v hv).2.2) hS
  refine ⟨m, x, y, z, hsf, ?_⟩
  have hVW (W : Finset (Fin n → ℕ)) (g : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → Fin n → ℕ)
      (v) (hv : v ∈ V) (h : #{v' ∈ V | g v = g v'} * #W = #V) : (#W : ℝ) ≤ #V := by
    rw [← h]
    exact_mod_cast Nat.le_mul_of_pos_left #W
      (card_pos.2 ⟨v, mem_filter.2 ⟨hv, rfl⟩⟩ : 0 < #{v' ∈ V | g v = g v'})
  have hw₀ : 0 < w := by linarith
  have hV₀ : (0 : ℝ) < #V := by linarith [hVW W₁ (fun v ↦ v.1) _ hv₀ (hfib₁ _ hv₀)]
  have hP : (0 : ℝ) < P := by exact_mod_cast hPprime.pos
  have hFle : (F : ℝ) ≤ 3 * (#V / w) := by
    have h (W : ℕ) (hW : w ≤ W) : ((#V / W : ℕ) : ℝ) ≤ #V / w :=
      Nat.cast_div_le.trans (div_le_div_of_nonneg_left hV₀.le hw₀ hW)
    simp only [F, Nat.cast_add]
    linarith [h _ hw₁, h _ hw₂, h _ hw₃]
  have hVw : 1 ≤ (#V : ℝ) / w :=
    (one_le_div hw₀).2 (hw₁.trans (hVW W₁ (fun v ↦ v.1) _ hv₀ (hfib₁ _ hv₀)))
  have hPle' : (P : ℝ) ≤ (36 + 2 * p) * (#V / w) := by
    have h₁ : (P : ℝ) ≤ 2 * (6 * F + p) := by exact_mod_cast hPle
    nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hlogP : log P ≤ log ((36 + 2 * p) * p ^ (3 * n)) := by
    refine log_le_log hP (hPle'.trans ?_)
    grw [div_le_self hV₀.le hw]
    exact_mod_cast Nat.mul_le_mul_left _ (card_baseTriples_le hp hf₀)
  have hE : exp (-4 * √(log ((36 + 2 * p) * p ^ (3 * n)))) ≤ exp (-4 * √(log P)) :=
    exp_le_exp.2 (by linarith [Real.sqrt_le_sqrt hlogP])
  have h3F : (P : ℝ) / 2 ≤ P - 3 * F := by
    have : (6 * F + p : ℝ) < P := by exact_mod_cast hPlt
    linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have h₁ : (#V : ℝ) * (P / 2 * exp (-4 * √(log P))) * (P / 2) ≤ m * P ^ 3 := by
    refine le_trans ?_ hm
    gcongr
  have h₂ : (#V : ℝ) * exp (-4 * √(log P)) ≤ 4 * m * P := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < P ^ 2 / 4)
    convert h₁ using 1 <;> ring
  rw [div_le_iff₀ (by positivity)]
  calc w * exp (-4 * √(log ((36 + 2 * p) * p ^ (3 * n))))
      ≤ w * exp (-4 * √(log P)) := by gcongr
    _ = w * (#V * exp (-4 * √(log P))) / #V := by field_simp
    _ ≤ w * (4 * m * ((36 + 2 * p) * (#V / w))) / #V := by grw [h₂, hPle']
    _ = m * (4 * (36 + 2 * p)) := by field_simp

end ArithmeticTriangleRemovalInVectorSpaces
