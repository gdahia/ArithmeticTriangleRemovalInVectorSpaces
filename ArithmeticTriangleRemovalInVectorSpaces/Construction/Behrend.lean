/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-!
# Large sets without arithmetic progressions in `ZMod P`

Behrend's construction gives a subset of `{0, …, (P - 1) / 2}` without three-term arithmetic
progressions with at least `(P / 2) exp (-4 √(log P))` elements. Its image in `ZMod P` has no
three-term arithmetic progressions either, since sums of two of its elements do not wrap around.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_finset_zmod_add_eq_add_lower_bound`: the set in
  `ZMod P`.
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- **Behrend's construction in `ZMod P`.** There is `S ⊆ ZMod P` without three-term arithmetic
progressions and with at least `(P / 2) exp (-4 √(log P))` elements. -/
lemma exists_finset_zmod_add_eq_add_lower_bound {P : ℕ} (hP : 0 < P) :
    ∃ S : Finset (ZMod P), (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = y + y → x = y) ∧
      P / 2 * exp (-4 * √(log P)) ≤ #S := by
  set L := (P + 1) / 2
  obtain ⟨t, ht, hcard, hfree⟩ := rothNumberNat_spec L
  have hlt {a : ℕ} (ha : a ∈ t) : a < L := mem_range.1 (ht ha)
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod P) t := by
    intro a ha b hb hab
    have := (ZMod.natCast_eq_natCast_iff' a b P).1 hab
    rwa [Nat.mod_eq_of_lt (by grind [hlt ha]), Nat.mod_eq_of_lt (by grind [hlt hb])] at this
  refine ⟨t.image Nat.cast, ?_, ?_⟩
  · simp only [mem_image]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ habc
    have := (ZMod.natCast_eq_natCast_iff' (a + c) (b + b) P).1 (by push_cast; exact habc)
    rw [Nat.mod_eq_of_lt (by grind [hlt ha, hlt hc]), Nat.mod_eq_of_lt (by grind [hlt hb])]
      at this
    rw [hfree ha hb hc this]
  · rw [card_image_of_injOn hinj, hcard]
    grw [← Behrend.roth_lower_bound]
    have hL : (P : ℝ) / 2 ≤ L := by
      rw [div_le_iff₀ two_pos]
      exact_mod_cast (by grind : P ≤ L * 2)
    have hL₀ : (0 : ℝ) < L := by exact_mod_cast (by grind : 0 < L)
    have hLP : (L : ℝ) ≤ P := by exact_mod_cast (by grind : L ≤ P)
    refine mul_le_mul hL (exp_le_exp.2 ?_) (exp_pos _).le hL₀.le
    linarith [Real.sqrt_le_sqrt (log_le_log hL₀ hLP)]

end ArithmeticTriangleRemovalInVectorSpaces
