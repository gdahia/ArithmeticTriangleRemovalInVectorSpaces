/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Hashing triples into a set without arithmetic progressions

Let `V` be a set of triples `(a, b, c)` of vectors in `{0, …, p - 1} ^ n` with `a + b + c` equal to
the all `p - 1` vector. A hash `θ = (h, α, β)` with values in `ZMod P` sends `a` to
`β + h ⬝ᵥ a` and `c` to `α + h ⬝ᵥ c`. The triples whose hashes agree and lie in a set `S` without
three-term arithmetic progressions, and which share no vector with another such triple, form a
multicolored sum-free family. Averaging over all hashes gives one where this family is large. This
is the construction of Section 4 of Kleinberg, Sawin and Speyer.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.hashedTriples V S θ`: the triples of `V` whose hashes
  agree and lie in `S`.
* `ArithmeticTriangleRemovalInVectorSpaces.isolatedTriples V S θ`: the hashed triples sharing no
  vector with another hashed triple.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.isMulticoloredSumFree_isolatedTriples`: the isolated
  triples form a multicolored sum-free family (Lemma 4.3 of Kleinberg, Sawin and Speyer).
* `ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_hash`: some hash leaves
  at least `|V| |S| (P - 3 F) / P ^ 3` isolated triples, where `F` bounds the number of triples
  sharing a given vector (Lemma 4.6 of Kleinberg, Sawin and Speyer).
-/

public section

open Finset Matrix

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n p P : ℕ}

/-- The triples of `V` whose hashes under `θ = (h, α, β)` agree and lie in `S`. -/
noncomputable def hashedTriples (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)))
    (S : Finset (ZMod P)) (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :=
  {v ∈ V | θ.2.2 + θ.1 ⬝ᵥ (fun r ↦ (v.1 r : ZMod P)) ∈ S ∧
    θ.2.1 + θ.1 ⬝ᵥ (fun r ↦ (v.2.2 r : ZMod P)) = θ.2.2 + θ.1 ⬝ᵥ (fun r ↦ (v.1 r : ZMod P))}

/-- Two triples share a vector if they agree in some coordinate. -/
def Shares (v v' : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) : Prop :=
  v.1 = v'.1 ∨ v.2.1 = v'.2.1 ∨ v.2.2 = v'.2.2

/-- The hashed triples that share no vector with another hashed triple. -/
noncomputable def isolatedTriples (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)))
    (S : Finset (ZMod P)) (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :=
  open Classical in {v ∈ hashedTriples V S θ | ∀ v' ∈ hashedTriples V S θ, Shares v v' → v' = v}

variable {V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))} {S : Finset (ZMod P)}

lemma dotProduct_add_eq_of_add_eq {a c a' c' : Fin n → ℕ} (h : ∀ r, a r + c r = a' r + c' r)
    (u : Fin n → ZMod P) :
    u ⬝ᵥ (fun r ↦ (a r : ZMod P)) + u ⬝ᵥ (fun r ↦ (c r : ZMod P)) =
      u ⬝ᵥ (fun r ↦ (a' r : ZMod P)) + u ⬝ᵥ (fun r ↦ (c' r : ZMod P)) := by
  rw [← dotProduct_add, ← dotProduct_add]
  congr 1
  ext r
  simp only [Pi.add_apply, ← Nat.cast_add, h r]

/-- The entries of a sum `a + b + c` that vanishes modulo `p` and whose entries sum to `n (p - 1)`
all equal `p - 1`. -/
lemma eq_sub_one_of_cast_eq_zero (hp : 0 < p) {a b c : Fin n → ℕ}
    (h : (fun r ↦ (a r : ZMod p)) + (fun r ↦ (b r : ZMod p)) + (fun r ↦ (c r : ZMod p) + 1) = 0)
    (hsum : ∑ r, (a r + b r + c r) = n * (p - 1)) (r : Fin n) : a r + b r + c r = p - 1 := by
  have hge (r : Fin n) : p - 1 ≤ a r + b r + c r := by
    have hr := congr_fun h r
    simp only [Pi.add_apply, Pi.zero_apply] at hr
    have := Nat.le_of_dvd (by grind)
      ((ZMod.natCast_eq_zero_iff (a r + b r + c r + 1) p).1 (by push_cast; rwa [add_assoc]))
    grind
  have := (sum_eq_sum_iff_of_le fun r (_ : r ∈ univ) ↦ hge r).1 (by simp [hsum])
  exact (this r (mem_univ r)).symm

lemma mem_hashedTriples {θ : (Fin n → ZMod P) × ZMod P × ZMod P}
    {v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} :
    v ∈ hashedTriples V S θ ↔ v ∈ V ∧ θ.2.2 + θ.1 ⬝ᵥ (fun r ↦ (v.1 r : ZMod P)) ∈ S ∧
      θ.2.1 + θ.1 ⬝ᵥ (fun r ↦ (v.2.2 r : ZMod P)) = θ.2.2 + θ.1 ⬝ᵥ (fun r ↦ (v.1 r : ZMod P)) :=
  mem_filter

lemma mem_isolatedTriples {θ : (Fin n → ZMod P) × ZMod P × ZMod P}
    {v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} :
    v ∈ isolatedTriples V S θ ↔
      v ∈ hashedTriples V S θ ∧ ∀ v' ∈ hashedTriples V S θ, Shares v v' → v' = v := by
  classical
  simp [isolatedTriples]

/-- **Lemma 4.3 of Kleinberg, Sawin and Speyer.** The isolated triples form a multicolored
sum-free family in `Fin n → ZMod p`, after shifting the third vectors by one. -/
lemma isMulticoloredSumFree_isolatedTriples (hp : 0 < p)
    (hV : ∀ v ∈ V, ∀ r, v.1 r + v.2.1 r + v.2.2 r = p - 1)
    (hclosed : ∀ v ∈ V, ∀ v' ∈ V, ∀ v'' ∈ V, (∀ r, v.1 r + v'.2.1 r + v''.2.2 r = p - 1) →
      (v.1, v'.2.1, v''.2.2) ∈ V)
    (hsum : ∀ v ∈ V, ∀ v' ∈ V, ∀ v'' ∈ V, ∑ r, (v.1 r + v'.2.1 r + v''.2.2 r) = n * (p - 1))
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = y + y → x = y)
    (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    IsMulticoloredSumFree (fun v : isolatedTriples V S θ ↦ fun r ↦ (v.1.1 r : ZMod p))
      (fun v r ↦ (v.1.2.1 r : ZMod p)) (fun v r ↦ (v.1.2.2 r : ZMod p) + 1) := by
  rintro ⟨⟨a₁, b₁, c₁⟩, hi⟩ ⟨⟨a₂, b₂, c₂⟩, hj⟩ ⟨⟨a₃, b₃, c₃⟩, hk⟩
  obtain ⟨hi, hiiso⟩ := mem_isolatedTriples.1 hi
  obtain ⟨hj, hjiso⟩ := mem_isolatedTriples.1 hj
  obtain ⟨hk, hkiso⟩ := mem_isolatedTriples.1 hk
  obtain ⟨hiV, hiS, hiC⟩ := mem_hashedTriples.1 hi
  obtain ⟨hjV, hjS, hjC⟩ := mem_hashedTriples.1 hj
  obtain ⟨hkV, hkS, hkC⟩ := mem_hashedTriples.1 hk
  obtain ⟨h, α, β⟩ := θ
  simp only [Subtype.mk.injEq]
  constructor
  · intro hsf
    have hent := eq_sub_one_of_cast_eq_zero hp hsf (hsum _ hiV _ hjV _ hkV)
    have hw := hclosed _ hiV _ hjV _ hkV hent
    have hrel := dotProduct_add_eq_of_add_eq (P := P) (a := a₁) (c := c₃) (a' := a₂) (c' := c₂)
      (fun r ↦ by grind [hV _ hjV r]) h
    simp only at hiS hjS hkS hiC hjC hkC hrel hw
    have hA : β + h ⬝ᵥ (fun r ↦ (a₁ r : ZMod P)) = β + h ⬝ᵥ (fun r ↦ (a₂ r : ZMod P)) :=
      hS _ hiS _ hjS _ (hkC ▸ hkS) (by linear_combination hrel + hjC)
    have hmem : (a₁, b₂, c₃) ∈ hashedTriples V S (h, α, β) :=
      mem_hashedTriples.2 ⟨hw, hiS, by linear_combination hrel + hjC - hA - hA⟩
    have h₁ := hiiso _ hmem (Or.inl rfl)
    have h₂ := hjiso _ hmem (Or.inr (Or.inl rfl))
    have h₃ := hkiso _ hmem (Or.inr (Or.inr rfl))
    exact ⟨h₁.symm.trans h₂, h₂.symm.trans h₃⟩
  · rintro ⟨h₁, h₂⟩
    simp only [Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₂
    ext r
    simp only [Pi.add_apply, Pi.zero_apply]
    have hr := hV _ hiV r
    dsimp only at hr
    have hr' : ((a₁ r + b₁ r + c₁ r + 1 : ℕ) : ZMod p) = 0 := by
      rw [hr, Nat.sub_add_cancel hp, ZMod.natCast_self]
    push_cast at hr'
    linear_combination hr'

/-- There are `|H| |S|` hashes `θ = (h, α, β)` with `h ∈ H` under which `a` and `c` have the same
hash in `S`. -/
lemma card_filter_hash [NeZero P] (a c : Fin n → ZMod P) (H : Finset (Fin n → ZMod P)) :
    #{θ : (Fin n → ZMod P) × ZMod P × ZMod P | θ.1 ∈ H ∧ θ.2.2 + θ.1 ⬝ᵥ a ∈ S ∧
      θ.2.1 + θ.1 ⬝ᵥ c = θ.2.2 + θ.1 ⬝ᵥ a} = #H * #S := by
  rw [← card_product]
  refine card_nbij' (fun θ ↦ (θ.1, θ.2.2 + θ.1 ⬝ᵥ a))
    (fun q ↦ (q.1, q.2 - q.1 ⬝ᵥ c, q.2 - q.1 ⬝ᵥ a)) ?_ ?_ ?_ ?_
  · rintro ⟨h, α, β⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_product, Set.mem_prod,
      mem_coe]
    grind
  · rintro ⟨h, s⟩
    simp only [coe_product, Set.mem_prod, mem_coe, coe_filter, mem_univ, true_and,
      Set.mem_ofPred_eq, sub_add_cancel]
    grind
  · rintro ⟨h, α, β⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Prod.mk.injEq,
      add_sub_cancel_right]
    grind
  · rintro ⟨h, s⟩
    simp

/-- A nonzero vector `u` is orthogonal to `P ^ n / P` vectors. -/
lemma card_filter_dotProduct_eq_zero_mul [Fact P.Prime] {u : Fin n → ZMod P} (hu : u ≠ 0) :
    #{h : Fin n → ZMod P | h ⬝ᵥ u = 0} * P = P ^ n := by
  obtain ⟨r, hr⟩ := Function.ne_iff.1 hu
  rw [Pi.zero_apply] at hr
  let f : (Fin n → ZMod P) →+ ZMod P := AddMonoidHom.mk' (· ⬝ᵥ u) fun a b ↦ add_dotProduct a b u
  have hf : Function.Surjective f := by
    intro z
    refine ⟨Pi.single r (z / u r), ?_⟩
    simp [f, single_dotProduct, div_mul_cancel₀ z hr]
  have := AddSubgroup.card_ker_mul_card_of_surjective (f := f) hf
  rw [Nat.card_eq_fintype_card, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_pi] at this
  simpa [Fintype.card_subtype, f] using this

lemma natCast_injective_of_lt {a a' : Fin n → ℕ} (ha : ∀ r, a r < P) (ha' : ∀ r, a' r < P)
    (h : (fun r ↦ (a r : ZMod P)) = fun r ↦ (a' r : ZMod P)) : a = a' := by
  ext r
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (congr_fun h r)
  rwa [Nat.mod_eq_of_lt (ha r), Nat.mod_eq_of_lt (ha' r)] at this

/-- Two distinct triples sharing a vector are both hashed only by `|S| P ^ n / P` hashes. -/
lemma card_filter_mem_hashedTriples_mul_le [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hV : ∀ v ∈ V, ∀ r, v.1 r + v.2.1 r + v.2.2 r = p - 1)
    {v v' : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} (hv : v ∈ V) (hv' : v' ∈ V) (hne : v ≠ v')
    (hsh : Shares v v') :
    #{θ | v ∈ hashedTriples V S θ ∧ v' ∈ hashedTriples V S θ} * P ≤ P ^ n * #S := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := v'
  have hlt {w : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} (hw : w ∈ V) (r : Fin n) :
      w.1 r < P ∧ w.2.2 r < P := by
    have := hV _ hw r
    grind
  set u : Fin n → ZMod P := if a = a' then (fun r ↦ (c r : ZMod P)) - fun r ↦ (c' r : ZMod P)
    else (fun r ↦ (a r : ZMod P)) - fun r ↦ (a' r : ZMod P)
  have hu : u ≠ 0 := by
    by_cases ha : a = a'
    · simp only [u, ha, ↓reduceIte]
      subst ha
      intro h0
      refine hne (Prod.ext rfl (Prod.ext ?_ (natCast_injective_of_lt (fun r ↦ (hlt hv r).2)
        (fun r ↦ (hlt hv' r).2) (sub_eq_zero.1 h0))))
      have hcc := natCast_injective_of_lt (fun r ↦ (hlt hv r).2) (fun r ↦ (hlt hv' r).2)
        (sub_eq_zero.1 h0)
      subst hcc
      ext r
      have h₁ := hV _ hv r
      have h₂ := hV _ hv' r
      simp only at h₁ h₂
      grind
    · simp only [u, ha, ↓reduceIte]
      exact fun h0 ↦ ha (natCast_injective_of_lt (fun r ↦ (hlt hv r).1) (fun r ↦ (hlt hv' r).1)
        (sub_eq_zero.1 h0))
  have hsub : ({θ | (a, b, c) ∈ hashedTriples V S θ ∧ (a', b', c') ∈ hashedTriples V S θ} :
      Finset ((Fin n → ZMod P) × ZMod P × ZMod P)) ⊆
      ({θ | θ.1 ∈ ({h | h ⬝ᵥ u = 0} : Finset (Fin n → ZMod P)) ∧
        θ.2.2 + θ.1 ⬝ᵥ (fun r ↦ (a r : ZMod P)) ∈ S ∧
        θ.2.1 + θ.1 ⬝ᵥ (fun r ↦ (c r : ZMod P)) = θ.2.2 + θ.1 ⬝ᵥ (fun r ↦ (a r : ZMod P))} :
        Finset ((Fin n → ZMod P) × ZMod P × ZMod P)) := by
    rintro ⟨h, α, β⟩
    simp only [mem_filter, mem_univ, true_and, mem_hashedTriples]
    rintro ⟨⟨-, hS₁, hC₁⟩, ⟨-, -, hC₂⟩⟩
    refine ⟨?_, hS₁, hC₁⟩
    by_cases ha : a = a'
    · simp only [u, ha, ↓reduceIte]
      subst ha
      rw [dotProduct_sub, sub_eq_zero]
      linear_combination hC₁ - hC₂
    simp only [u, ha, ↓reduceIte]
    rw [dotProduct_sub, sub_eq_zero]
    rcases hsh with h₁ | h₂ | h₃
    · exact absurd h₁ ha
    · dsimp only at h₂
      subst h₂
      have h2 : (2 : ZMod P) ≠ 0 := by
        intro h2
        have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 P).1 (by exact_mod_cast h2))
        grind
      have hac (r : Fin n) : a r + c r = a' r + c' r := by
        have h₁ := hV _ hv r
        have h₂ := hV _ hv' r
        dsimp only at h₁ h₂
        grind
      refine mul_left_cancel₀ h2 ?_
      linear_combination dotProduct_add_eq_of_add_eq hac h - hC₁ + hC₂
    · dsimp only at h₃
      subst h₃
      linear_combination hC₂ - hC₁
  grw [card_le_card hsub, card_filter_hash, mul_right_comm, card_filter_dotProduct_eq_zero_mul hu]

/-- Exchanging the sums over hashes and triples. -/
lemma sum_card_filter_comm {α β : Type*} [Fintype α] (s : Finset β) (q : α → β → Prop)
    [∀ a b, Decidable (q a b)] : ∑ a, #{b ∈ s | q a b} = ∑ b ∈ s, #{a | q a b} := by
  simp only [card_filter]
  exact sum_comm

lemma sum_card_hashedTriples [NeZero P] :
    ∑ θ, #(hashedTriples V S θ) = #V * (P ^ n * #S) := by
  classical
  simp only [hashedTriples]
  rw [sum_card_filter_comm, ← smul_eq_mul, ← sum_const]
  congr with v
  have := card_filter_hash (S := S) (fun r ↦ (v.1 r : ZMod P)) (fun r ↦ (v.2.2 r : ZMod P)) univ
  simp only [mem_univ, true_and, card_univ, Fintype.card_pi, ZMod.card, prod_const,
    Fintype.card_fin] at this
  rw [← this]

/-- The pairs of distinct triples of `V` sharing a vector. -/
noncomputable def sharingPairs (V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))) :
    Finset (((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) ×
      ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))) :=
  open Classical in {q ∈ V ×ˢ V | q.1 ≠ q.2 ∧ Shares q.1 q.2}

lemma card_sharingPairs_le {F : ℕ} (hF₁ : ∀ v ∈ V, #{v' ∈ V | v.1 = v'.1} ≤ F)
    (hF₂ : ∀ v ∈ V, #{v' ∈ V | v.2.1 = v'.2.1} ≤ F)
    (hF₃ : ∀ v ∈ V, #{v' ∈ V | v.2.2 = v'.2.2} ≤ F) :
    #(sharingPairs V) ≤ #V * (3 * F) := by
  classical
  rw [sharingPairs, card_filter, sum_product, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro v hv
  rw [← card_filter]
  have hsub : {v' ∈ V | v ≠ v' ∧ Shares v v'} ⊆
      {v' ∈ V | v.1 = v'.1} ∪ {v' ∈ V | v.2.1 = v'.2.1} ∪ {v' ∈ V | v.2.2 = v'.2.2} := by
    intro v' hv'
    rw [mem_filter] at hv'
    obtain ⟨hv'V, -, h | h | h⟩ := hv'
    all_goals simp [hv'V, h]
  grw [card_le_card hsub, card_union_le, card_union_le, hF₁ v hv, hF₂ v hv, hF₃ v hv]
  grind

/-- A hashed triple is isolated unless it is the first member of a pair of hashed triples sharing
a vector. -/
lemma card_hashedTriples_le (θ : (Fin n → ZMod P) × ZMod P × ZMod P) :
    #(hashedTriples V S θ) ≤ #(isolatedTriples V S θ) +
      #{q ∈ sharingPairs V | q.1 ∈ hashedTriples V S θ ∧ q.2 ∈ hashedTriples V S θ} := by
  classical
  refine (card_le_card (t := isolatedTriples V S θ ∪
    {q ∈ sharingPairs V | q.1 ∈ hashedTriples V S θ ∧ q.2 ∈ hashedTriples V S θ}.image Prod.fst)
    ?_).trans ?_
  swap
  · grw [card_union_le, card_image_le]
  intro v hv
  rw [mem_union, mem_image]
  by_cases hiso : v ∈ isolatedTriples V S θ
  · exact Or.inl hiso
  right
  simp only [mem_isolatedTriples, hv, true_and, not_forall] at hiso
  obtain ⟨v', hv', hsh, hne⟩ := hiso
  refine ⟨(v, v'), mem_filter.2 ⟨mem_filter.2 ⟨mem_product.2 ⟨(mem_filter.1 hv).1,
    (mem_filter.1 hv').1⟩, Ne.symm hne, hsh⟩, hv, hv'⟩, rfl⟩

/-- **Lemma 4.6 of Kleinberg, Sawin and Speyer.** Some hash leaves at least
`|V| |S| (P - 3 F) / P ^ 3` isolated triples, which form a multicolored sum-free family. -/
lemma exists_isMulticoloredSumFree_of_hash [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hV : ∀ v ∈ V, ∀ r, v.1 r + v.2.1 r + v.2.2 r = p - 1)
    (hclosed : ∀ v ∈ V, ∀ v' ∈ V, ∀ v'' ∈ V, (∀ r, v.1 r + v'.2.1 r + v''.2.2 r = p - 1) →
      (v.1, v'.2.1, v''.2.2) ∈ V)
    (hsum : ∀ v ∈ V, ∀ v' ∈ V, ∀ v'' ∈ V, ∑ r, (v.1 r + v'.2.1 r + v''.2.2 r) = n * (p - 1))
    {F : ℕ} (hF₁ : ∀ v ∈ V, #{v' ∈ V | v.1 = v'.1} ≤ F)
    (hF₂ : ∀ v ∈ V, #{v' ∈ V | v.2.1 = v'.2.1} ≤ F) (hF₃ : ∀ v ∈ V, #{v' ∈ V | v.2.2 = v'.2.2} ≤ F)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = y + y → x = y) :
    ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p), IsMulticoloredSumFree x y z ∧
      (#V * #S * (P - 3 * F) : ℝ) ≤ m * P ^ 3 := by
  classical
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hpairs : P * ∑ θ, #{q ∈ sharingPairs V | q.1 ∈ hashedTriples V S θ ∧
      q.2 ∈ hashedTriples V S θ} ≤ #V * (3 * F) * (P ^ n * #S) := by
    rw [sum_card_filter_comm, mul_sum]
    grw [sum_le_sum (g := fun _ ↦ P ^ n * #S), sum_const, smul_eq_mul,
      card_sharingPairs_le hF₁ hF₂ hF₃]
    intro q hq
    obtain ⟨hq, hne, hsh⟩ := mem_filter.1 hq
    obtain ⟨hq₁, hq₂⟩ := mem_product.1 hq
    rw [mul_comm]
    exact card_filter_mem_hashedTriples_mul_le hp hpP hV hq₁ hq₂ hne hsh
  have hle : (#V * (P ^ n * #S) : ℝ) ≤ ∑ θ, ((#(isolatedTriples V S θ) : ℝ) +
      #{q ∈ sharingPairs V | q.1 ∈ hashedTriples V S θ ∧ q.2 ∈ hashedTriples V S θ}) := by
    rw [(by exact_mod_cast sum_card_hashedTriples :
      (∑ θ, (#(hashedTriples V S θ) : ℝ)) = #V * (P ^ n * #S)).symm]
    exact sum_le_sum fun θ _ ↦ by exact_mod_cast card_hashedTriples_le θ
  rw [sum_add_distrib] at hle
  have hpairs' : (P : ℝ) * ∑ θ, (#{q ∈ sharingPairs V | q.1 ∈ hashedTriples V S θ ∧
      q.2 ∈ hashedTriples V S θ} : ℝ) ≤ #V * (3 * F) * (P ^ n * #S) := by
    exact_mod_cast hpairs
  obtain ⟨θ, -, hθ⟩ := exists_le_of_sum_le (s := univ) univ_nonempty
    (f := fun _ ↦ (#V * #S * (P - 3 * F) : ℝ) / P ^ 3)
    (g := fun θ ↦ (#(isolatedTriples V S θ) : ℝ)) (by
      rw [sum_const, card_univ, nsmul_eq_mul]
      simp only [Fintype.card_prod, Fintype.card_pi, ZMod.card, prod_const, card_univ,
        Fintype.card_fin]
      push_cast
      rw [(by field_simp : (P : ℝ) ^ n * (P * P) * (#V * #S * (P - 3 * F) / P ^ 3) =
        P ^ n * (#V * #S * (P - 3 * F)) / P), div_le_iff₀ hP]
      nlinarith)
  rw [div_le_iff₀ (by positivity)] at hθ
  set s := isolatedTriples V S θ
  refine ⟨#s, _, _, _, (isMulticoloredSumFree_isolatedTriples (by grind) hV hclosed hsum hS
    θ).comp s.equivFin.symm.injective, hθ⟩

end ArithmeticTriangleRemovalInVectorSpaces
