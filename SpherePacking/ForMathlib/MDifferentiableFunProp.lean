module

public import Mathlib.NumberTheory.ModularForms.Basic

/-!
# `fun_prop` Lemmas for Manifold Differentiability

`fun_prop` lemmas for manifold differentiability of functions on the upper half-plane.
-/

@[expose] public section

open scoped Manifold UpperHalfPlane

/-- Modular forms are `MDifferentiable`; the generic form lets `fun_prop` handle coerced modular
forms such as Mathlib's `ModularForm.E₄`. -/
theorem ModularForm.mdifferentiable {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ}
    (f : ModularForm Γ k) : MDiff f := f.holo'

/-
Register `MDifferentiable` as a `fun_prop` so that we can use it in `fun_prop`-based proofs.
To be upstreamed in mathlib PR [#33808](https://github.com/leanprover-community/mathlib4/pull/33808)
-/
attribute [fun_prop] MDifferentiable

attribute [fun_prop]
  MDifferentiable.add
  MDifferentiable.sub
  MDifferentiable.neg
  MDifferentiable.mul
  MDifferentiable.pow
  MDifferentiable.const_smul
  mdifferentiable_const
  ModularForm.mdifferentiable
