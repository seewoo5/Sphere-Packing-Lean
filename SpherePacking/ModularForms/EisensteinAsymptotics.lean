/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Derivative
public import SpherePacking.ModularForms.Eisenstein

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import SpherePacking.ForMathlib.AtImInfty
import SpherePacking.ModularForms.E2
import SpherePacking.ModularForms.QExpansion

/-!
# Asymptotic Behavior of Eisenstein Series

This file establishes the asymptotic behavior of Eisenstein series and of Serre derivatives as
`z → i∞`. (`E₂ → 1` is Mathlib's `EisensteinSeries.tendsto_E2_atImInfty`.)

## Main results

* `E₂_sub_one_isBigO_exp` : `E₂ - 1 = O(exp(-2π im z))` at `i∞`
* `E₄_tendsto_one_atImInfty`, `E₆_tendsto_one_atImInfty` : `E₄, E₆ → 1` at `i∞`
* `E₄_sub_isBigO`, `E₆_sub_isBigO` : `E₄ = 1 + 240q + 2160q² + O(q³)` and
  `E₆ = 1 - 504q - 16632q² + O(q³)` at `i∞`, where `q = e^{2πiz}`
* `E₂_mul_E₄_sub_E₆_sub_isBigO` : `E₂E₄ - E₆ = 720q + O(q²)` at `i∞`
* `serreDerivative_tendsto_of_tendsto` : the limit of `∂ₖ f` at `i∞` from that of `f`
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm hiding E₄ E₆
open Real Complex CongruenceSubgroup Filter SlashInvariantFormClass ModularFormClass

open scoped Manifold MatrixGroups ArithmeticFunction.sigma
open Derivative

noncomputable section

/-! ## Limits of Eisenstein series at infinity -/

/-- If f = O(exp(-c * Im z)) as z → i∞ for c > 0, then f → 0 at i∞. -/
lemma tendsto_zero_of_exp_decay {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Filter.Tendsto f atImInfty (nhds 0) := by
  have h : Filter.Tendsto (fun y : ℝ => Real.exp (-c * y)) Filter.atTop (nhds 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  exact hO.trans_tendsto (h.comp tendsto_im_atImInfty)

/-- A modular form tends to its value at infinity as z → i∞. -/
lemma modular_form_tendsto_atImInfty {k : ℤ} (f : ModularForm (Gamma 1) k) :
    Filter.Tendsto f.toFun atImInfty (nhds ((qExpansion 1 f).coeff 0)) := by
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  have hΓ : (1 : ℝ) ∈ (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ one_mem_strictPeriods_SL
  rw [qExpansion_coeff_zero (by norm_num : (0 : ℝ) < 1)
    (ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num) hΓ)
    (periodic_comp_ofComplex f hΓ)]
  simpa using (tendsto_zero_of_exp_decay hc hO).add_const (valueAtInfty f.toFun)

/-- E₂ - 1 = O(exp(-2π·Im z)) at infinity. -/
lemma E₂_sub_one_isBigO_exp : (fun z : ℍ => E₂ z - 1) =O[atImInfty]
    fun z => Real.exp (-(2 * π) * z.im) := by
  have h := exp_decay_sub_atImInfty one_pos EisensteinSeries.E2_periodic
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  simpa [neg_mul, show valueAtInfty E₂ = 1 from
    EisensteinSeries.tendsto_E2_atImInfty.limUnder_eq] using h

/-- E₄ → 1 at i∞. -/
lemma E₄_tendsto_one_atImInfty : Filter.Tendsto E₄.toFun atImInfty (nhds 1) :=
  E4_q_exp_zero ▸ modular_form_tendsto_atImInfty E₄

/-- E₆ → 1 at i∞. -/
lemma E₆_tendsto_one_atImInfty : Filter.Tendsto E₆.toFun atImInfty (nhds 1) :=
  E6_q_exp_zero ▸ modular_form_tendsto_atImInfty E₆

/-! ## Boundedness lemmas -/

/-- E₄ is bounded at infinity (as a modular form). -/
lemma E₄_isBoundedAtImInfty : IsBoundedAtImInfty E₄.toFun :=
  ModularFormClass.bdd_at_infty E₄

/-- E₆ is bounded at infinity (as a modular form). -/
lemma E₆_isBoundedAtImInfty : IsBoundedAtImInfty E₆.toFun :=
  ModularFormClass.bdd_at_infty E₆

/-! ## Limit of the Serre derivative at infinity -/

/-- General limit: if `f → c` at i∞ and f is holomorphic and bounded, then `∂ₖ f → -k*c/12`.

This is the continuous mapping theorem applied to `∂ₖ f = D f - (k/12) * E₂ * f`:
- D f → 0 (Cauchy estimate from boundedness)
- E₂ → 1
- f → c
Therefore `∂ₖ f → 0 - (k/12) * 1 * c = -k*c/12`. -/
lemma serreDerivative_tendsto_of_tendsto (k : ℤ) (f : ℍ → ℂ) (c : ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds c)) :
    Filter.Tendsto (serreDerivative k f) atImInfty (nhds (-(k : ℂ) * c / 12)) := by
  rw [show serreDerivative k f = fun z => D f z - (k : ℂ) * 12⁻¹ * E₂ z * f z from
    serreDerivative_eq k f, show -(k : ℂ) * c / 12 = 0 - (k : ℂ) * 12⁻¹ * 1 * c by ring]
  exact Filter.Tendsto.sub (isZeroAtImInfty_normalizedDerivOfComplex hf_holo hf_bdd)
    ((tendsto_const_nhds.mul EisensteinSeries.tendsto_E2_atImInfty).mul hf_lim)

/-- Special case: if `f → 1` at i∞, then `∂ₖ f → -k/12`. -/
lemma serreDerivative_tendsto_neg_k_div_12 (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 1)) :
    Filter.Tendsto (serreDerivative k f) atImInfty (nhds (-(k : ℂ) / 12)) := by
  simpa using serreDerivative_tendsto_of_tendsto k f 1 hf_holo hf_bdd hf_lim

/-- Special case: if `f → 0` at i∞, then `∂ₖ f → 0`. -/
lemma serreDerivative_tendsto_zero_of_tendsto_zero (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 0)) :
    Filter.Tendsto (serreDerivative k f) atImInfty (nhds 0) := by
  simpa using serreDerivative_tendsto_of_tendsto k f 0 hf_holo hf_bdd hf_lim

/-! ## Generic q-expansion summability -/

/-- Summability of (m+1)^k * exp(-2πm) via comparison with shifted sum. -/
lemma summable_pow_shift (k : ℕ) :
    Summable fun m : ℕ => (m + 1 : ℝ) ^ k * rexp (-2 * π * m) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul k (by positivity : 0 < 2 * π)
  have h_eq : ∀ m : ℕ, (m + 1 : ℝ) ^ k * rexp (-2 * π * m) =
      rexp (2 * π) * ((m + 1) ^ k * rexp (-2 * π * (m + 1))) := fun m => by
    rw [show (-2 : ℝ) * π * m = 2 * π + -2 * π * (m + 1) by ring, Real.exp_add]
    ring
  simp_rw [h_eq]
  exact ((h.comp_injective Nat.succ_injective).congr fun i => by
    simp [Function.comp_apply, Nat.succ_eq_add_one]).mul_left _

/-- The coefficients `mʲ σₖ(m)` are summable against `e^{-2πm}`. -/
lemma summable_pow_mul_sigma (j k : ℕ) :
    Summable fun m : ℕ ↦ ‖(m : ℂ) ^ j * (σ k m : ℂ)‖ * rexp (-2 * π * m) := by
  refine .of_nonneg_of_le (fun _ ↦ by positivity) (fun m ↦ ?_) (summable_pow_shift (j + k + 1))
  rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast, add_assoc, pow_add]
  gcongr
  · linarith
  · calc _ ≤ (m : ℝ) ^ (k + 1) := mod_cast ArithmeticFunction.sigma_le_pow_succ k m
      _ ≤ _ := by gcongr; linarith

/-! ## Low-order `q`-expansions of `E₄`, `E₆` and `E₂E₄ - E₆` -/

/-- `E₄ = 1 + 240 q + 2160 q² + O(q³)` at `i∞`. -/
lemma E₄_sub_isBigO : (fun z : ℍ ↦ E₄ z - (1 + 240 * cexp (2 * π * I * z) +
    2160 * cexp (2 * π * I * z) ^ 2)) =O[atImInfty] fun z ↦ cexp (2 * π * I * z) ^ 3 := by
  refine ((QExp.isBigO_tsum_sub_sum_range (a := fun m ↦ σ 3 m)
    (by simpa using summable_pow_mul_sigma 0 3) 3).const_mul_left 240).congr_left fun z ↦ ?_
  rw [E₄_sigma_qexp, tsum_pnat_eq_tsum_of_eq_zero
    (f := fun n : ℕ ↦ σ 3 n * cexp (2 * π * I * n * z)) (by simp)]
  simp [Finset.sum_range_succ, ← Complex.exp_natCast_mul, show σ 3 2 = 9 by decide, mul_comm,
    mul_left_comm]
  ring

/-- `E₆ = 1 - 504 q - 16632 q² + O(q³)` at `i∞`. -/
lemma E₆_sub_isBigO : (fun z : ℍ ↦ E₆ z - (1 - 504 * cexp (2 * π * I * z) -
    16632 * cexp (2 * π * I * z) ^ 2)) =O[atImInfty] fun z ↦ cexp (2 * π * I * z) ^ 3 := by
  refine ((QExp.isBigO_tsum_sub_sum_range (a := fun m ↦ (σ 5 m : ℂ))
    (by simpa using summable_pow_mul_sigma 0 5) 3).const_mul_left
    (-504)).congr_left fun z ↦ ?_
  rw [E₆_sigma_qexp, tsum_pnat_eq_tsum_of_eq_zero
    (f := fun n : ℕ ↦ σ 5 n * cexp (2 * π * I * n * z)) (by simp)]
  simp [Finset.sum_range_succ, ← Complex.exp_natCast_mul, show σ 5 2 = 33 by decide, mul_comm,
    mul_left_comm]
  ring

/-- `E₂ E₄ - E₆ = 720 q + O(q²)` at `i∞`. -/
lemma E₂_mul_E₄_sub_E₆_sub_isBigO : (fun z : ℍ ↦ E₂ z * E₄ z - E₆ z - 720 * cexp (2 * π * I * z))
    =O[atImInfty] fun z ↦ cexp (2 * π * I * z) ^ 2 := by
  refine ((QExp.isBigO_tsum_sub_sum_range (a := fun m ↦ m * σ 3 m)
    (by simpa using summable_pow_mul_sigma 1 3) 2).const_mul_left 720).congr_left fun z ↦ ?_
  rw [E₂_mul_E₄_sub_E₆_qexp, tsum_pnat_eq_tsum_of_eq_zero
    (f := fun n : ℕ ↦ n * σ 3 n * cexp (2 * π * I * n * z)) (by simp)]
  simp [Finset.sum_range_succ, mul_comm, mul_left_comm]
  ring
