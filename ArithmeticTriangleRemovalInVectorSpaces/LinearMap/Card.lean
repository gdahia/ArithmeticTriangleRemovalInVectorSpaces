/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Linear maps vanishing at independent vectors

For linearly independent `v : Fin r → V`, the map `A ↦ (A (v i))ᵢ` from `V →ₗ[K] W` to
`Fin r → W` is surjective. Hence the linear maps that vanish at `v 0, …, v (r - 1)` form a
proportion `1 / Nat.card W ^ r` of all linear maps. A uniformly random linear map `A` stands in for
the random subspace of Fox and Lovász: its kernel contains `r` given independent vectors with
probability `Nat.card W ^ (-r)`.

## Main statements

* `LinearMap.finite_of_finite`: there are finitely many linear maps between finite modules.
* `LinearIndependent.exists_linearMap_apply_eq`: prescribing the values of a linear map at
  linearly independent vectors.
* `LinearIndependent.natCard_mul_pow_eq_natCard`: the count of linear maps vanishing at `r`
  linearly independent vectors.
-/

public section

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {r : ℕ} {v : Fin r → V}

/-- There are finitely many linear maps between finite modules. -/
instance LinearMap.finite_of_finite [Finite V] [Finite W] : Finite (V →ₗ[K] W) :=
  Finite.of_injective _ DFunLike.coe_injective

/-- A linear map can take any prescribed values at linearly independent vectors. -/
lemma LinearIndependent.exists_linearMap_apply_eq (hv : LinearIndependent K v) (w : Fin r → W) :
    ∃ A : V →ₗ[K] W, ∀ i, A (v i) = w i := by
  obtain ⟨A, hA⟩ := LinearMap.exists_extend ((Basis.span hv).constr K w)
  refine ⟨A, ?_⟩
  intro i
  have := congr($hA (Basis.span hv i))
  rwa [Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Basis.span_apply] at this

/-- The linear maps vanishing at `r` linearly independent vectors form a proportion
`1 / Nat.card W ^ r` of all linear maps. -/
lemma LinearIndependent.natCard_mul_pow_eq_natCard (hv : LinearIndependent K v) :
    Nat.card {A : V →ₗ[K] W // ∀ i, A (v i) = 0} * Nat.card W ^ r = Nat.card (V →ₗ[K] W) := by
  let Φ : (V →ₗ[K] W) →ₗ[K] Fin r → W := LinearMap.pi fun i ↦ LinearMap.applyₗ (v i)
  have hΦ : Function.Surjective Φ := fun w ↦ by
    obtain ⟨A, hA⟩ := hv.exists_linearMap_apply_eq w
    exact ⟨A, funext hA⟩
  have hker : Nat.card {A : V →ₗ[K] W // ∀ i, A (v i) = 0} = Nat.card (LinearMap.ker Φ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun A ↦ by simp [Φ, funext_iff])
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker Φ),
    Nat.card_congr (Φ.quotKerEquivOfSurjective hΦ).toEquiv, Nat.card_fun, Nat.card_fin, hker,
    mul_comm]
