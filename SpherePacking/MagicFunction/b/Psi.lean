/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Raphael Appenzeller, Seewoo Lee
-/
module

public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.ModularForms.FG

import SpherePacking.ForMathlib.SlashActions
import SpherePacking.ForMathlib.AtImInfty
import SpherePacking.ModularForms.JacobiTheta.MDifferentiable
import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.JacobiTheta.Basic
import SpherePacking.ModularForms.JacobiTheta.JacobiIdentity

/-!
# The ψ Functions

In this file, we define the functions `ψI`, `ψT` and `ψS` that are defined using the
Jacobi theta functions and are used in the definition of the -1-eigenfunction `b`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Filter Complex Real Matrix ModularGroup ModularForm SlashAction MatrixGroups
open scoped Manifold

noncomputable section defs

/-- The auxiliary function `h = 128 (H₃ + H₄) / H₂ ^ 2`, from which the `ψ` functions are obtained
via slash actions. -/
def h : ℍ → ℂ := 128 • (H₃ + H₄) / (H₂ ^ 2)

/-- `ψI = h - h ∣[-2] (S * T)`. -/
def ψI : ℍ → ℂ := h - h ∣[-2] (S * T)

/-- `ψT = ψI ∣[-2] T`. -/
def ψT : ℍ → ℂ := ψI ∣[-2] T

/-- `ψS = ψI ∣[-2] S`. -/
def ψS : ℍ → ℂ := ψI ∣[-2] S

/-- `ψI`, extended by zero to a function on `ℂ`. -/
def ψI' (z : ℂ) : ℂ := if hz : 0 < z.im then ψI ⟨z, hz⟩ else 0

/-- `ψS`, extended by zero to a function on `ℂ`. -/
def ψS' (z : ℂ) : ℂ := if hz : 0 < z.im then ψS ⟨z, hz⟩ else 0

/-- `ψT`, extended by zero to a function on `ℂ`. -/
def ψT' (z : ℂ) : ℂ := if hz : 0 < z.im then ψT ⟨z, hz⟩ else 0

lemma ψI'_def {z : ℂ} (hz : 0 < z.im) : ψI' z = ψI ⟨z, hz⟩ := by simp [ψI', hz]
lemma ψS'_def {z : ℂ} (hz : 0 < z.im) : ψS' z = ψS ⟨z, hz⟩ := by simp [ψS', hz]
lemma ψT'_def {z : ℂ} (hz : 0 < z.im) : ψT' z = ψT ⟨z, hz⟩ := by simp [ψT', hz]

end defs

section eq

/- We express `ψI`, `ψT`, `ψS` in terms of the `H`-functions directly (Lemma 7.16 in the blueprint).
The proofs distribute the slash action over `•`, `+`, `-`, `/` and `^ 2` at the level of functions,
so that only the `S`- and `T`-actions on `H₂`, `H₃`, `H₄` remain; the resulting identity of
functions is then checked pointwise by `ring`. `nsmul_eq_mul` is excluded from `simp` so that
`128 • F` is not turned into a product (whose slash action has no determined weight split) before
`SL_smul_slash` pulls the scalar out. -/

/-- The weight `-2` slash action of a quotient `F / G ^ 2` of two weight `2` functions, with the
weight in the form `simp` can match. `grind` matches the two splitting lemmas on their right-hand
sides, so the compound weight `2 - 2 * 2` never has to be matched syntactically against `-2`. -/
private lemma div_sq_slash (γ : SL(2, ℤ)) (F G : ℍ → ℂ) :
    (F / G ^ 2) ∣[(-2 : ℤ)] γ = F ∣[(2 : ℤ)] γ / (G ∣[(2 : ℤ)] γ) ^ 2 := by
  grind [=_ div_slash_SL2, =_ pow_slash_SL2]

lemma ψI_eq : ψI = 128 • ((H₃ + H₄) / (H₂ ^ 2) + (H₄ - H₂) / H₃ ^ 2) := by
  ext z
  simp [-nsmul_eq_mul, ψI, h, slash_mul, div_sq_slash, H₂_S_action, H₃_S_action, H₄_S_action,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ring

lemma ψT_eq : ψT = 128 * ((H₃ + H₄) / (H₂ ^ 2) + (H₂ + H₃) / H₄ ^ 2) := by
  ext z
  simp [-nsmul_eq_mul, ψT, ψI_eq, div_sq_slash, H₂_T_action, H₃_T_action, H₄_T_action]
  ring

lemma ψS_eq : ψS = 128 * ((H₄ - H₂) / (H₃ ^ 2) - (H₂ + H₃) / H₄ ^ 2) := by
  ext z
  simp [-nsmul_eq_mul, ψS, ψI_eq, div_sq_slash, H₂_S_action, H₃_S_action, H₄_S_action]
  ring

/-- `ψS` in terms of the weight-10 form `G` and the discriminant: `ψS = -G / (2Δ)`.
This follows from `ψS_eq`, the Jacobi identity `H₂ + H₄ = H₃`, and `Δ = (H₂H₃H₄)² / 256`. -/
theorem ψS_eq_neg_one_half_smul_G_div_disc : ψS = (-1 / 2 : ℂ) • G / Δ := by
  ext z
  have hΔ := Δ_eq_H₂_H₃_H₄ z
  obtain ⟨⟨h₂, h₃⟩, h₄⟩ : (H₂ z ≠ 0 ∧ H₃ z ≠ 0) ∧ H₄ z ≠ 0 := by
    simpa [hΔ, not_or] using ModularForm.discriminant_ne_zero z
  have hJ : H₃ z = H₂ z + H₄ z := (congrFun jacobi_identity z).symm
  rw [hJ] at h₃ hΔ
  rw [ψS_eq, G_eq]
  simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hJ, hΔ]
  field

/-- The identity that combines the vertical tails in Proposition 7.40. -/
lemma ψT_add_ψS : ψT + ψS = ψI := by
  rw [ψT_eq, ψS_eq, ψI_eq]
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply,
    Pi.ofNat_apply, Pi.smul_apply, nsmul_eq_mul]
  ring

/-- The normalized discriminant tends to one at the cusp. -/
private lemma normalized_discriminant_tendsto :
    Filter.Tendsto (fun z : ℍ ↦ Δ z / cexp (2 * π * I * z)) atImInfty
      (nhds 1) := by
  have hre (z : ℍ) : Δ z / cexp (2 * π * I * z) =
      (H₂ z / cexp (π * I * z)) ^ 2 * (H₃ z) ^ 2 * (H₄ z) ^ 2 / 256 := by
    rw [Δ_eq_H₂_H₃_H₄, ← show cexp (π * I * z) ^ 2 = cexp (2 * π * I * z) by
      rw [← Complex.exp_nat_mul]
      push_cast
      ring_nf]
    ring
  simp_rw [hre]
  have hlim := (((H₂_div_exp_tendsto.pow 2).mul (H₃_tendsto_atImInfty.pow 2)).mul
    (H₄_tendsto_atImInfty.pow 2)).div_const (256 : ℂ)
  convert hlim using 1
  norm_num

/-- The normalized leading term of `ψS` at the cusp. -/
lemma ψS_div_exp_tendsto :
    Filter.Tendsto (fun z : ℍ ↦ ψS z / cexp (π * I * z)) atImInfty
      (nhds (-10240)) := by
  have hre (z : ℍ) : ψS z / cexp (π * I * z) =
      (-1 / 2 : ℂ) * ((G z / cexp (2 * π * I * (3 / 2) * z)) /
        (Δ z / cexp (2 * π * I * z))) := by
    rw [ψS_eq_neg_one_half_smul_G_div_disc]
    simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    have he : 2 * (π : ℂ) * I * z + π * I * z = 2 * π * I * (3 / 2) * z := by
      ring
    rw [← he, Complex.exp_add]
    field_simp [Complex.exp_ne_zero]
  simp_rw [hre]
  have hlim := (G_vanishing_order.div normalized_discriminant_tendsto one_ne_zero).const_mul
    (-1 / 2 : ℂ)
  convert hlim using 1
  norm_num

/-- The leading term of `ψI` at the cusp, normalized by the polar exponential. -/
lemma ψI_mul_exp_tendsto :
    Filter.Tendsto (fun z : ℍ ↦ ψI z * cexp (2 * π * I * z)) atImInfty (nhds 1) := by
  have he (z : ℍ) : cexp (2 * π * I * z) = cexp (π * I * z) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hExp : Filter.Tendsto (fun z : ℍ ↦ cexp (2 * π * I * z)) atImInfty (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -(2 * π) < 0 from neg_lt_zero.mpr (by positivity)))).comp
      Filter.tendsto_im_atImInfty
    convert h using 1
    ext z
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hre (z : ℍ) : ψI z * cexp (2 * π * I * z) =
      128 * ((H₃ z + H₄ z) / (H₂ z / cexp (π * I * z)) ^ 2 +
        ((H₄ z - H₂ z) / H₃ z ^ 2) * cexp (2 * π * I * z)) := by
    rw [congrFun ψI_eq z]
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.add_apply, Pi.sub_apply,
      Pi.div_apply, Pi.pow_apply]
    rw [he, div_pow, div_div_eq_mul_div]
    ring
  simp_rw [hre]
  have h₁ := (H₃_tendsto_atImInfty.add H₄_tendsto_atImInfty).div
    (H₂_div_exp_tendsto.pow 2) (by norm_num)
  have h₂ := ((H₄_tendsto_atImInfty.sub H₂_tendsto_atImInfty).div
    (H₃_tendsto_atImInfty.pow 2) (by norm_num)).mul hExp
  convert (h₁.add h₂).const_mul (128 : ℂ) using 1
  norm_num

lemma ψI_mdifferentiable : MDiff ψI := by
  have h₂ (z : ℍ) : H₂ z ≠ 0 := by
    intro hz
    simpa [Δ_eq_H₂_H₃_H₄, hz] using ModularForm.discriminant_ne_zero z
  have h₃ (z : ℍ) : H₃ z ≠ 0 := by
    intro hz
    simpa [Δ_eq_H₂_H₃_H₄, hz] using ModularForm.discriminant_ne_zero z
  rw [ψI_eq]
  have h :=
    ((H₃_MDifferentiable.add H₄_MDifferentiable).div
      (H₂_MDifferentiable.pow 2) (fun z ↦ pow_ne_zero 2 (h₂ z))).add
    ((H₄_MDifferentiable.sub H₂_MDifferentiable).div
      (H₃_MDifferentiable.pow 2) (fun z ↦ pow_ne_zero 2 (h₃ z)))
  simpa only [Nat.cast_smul_eq_nsmul] using h.const_smul ((128 : ℕ) : ℂ)

lemma ψI_continuous : Continuous ψI := ψI_mdifferentiable.continuous

end eq

section rels

lemma ψS_slash_S : ψS ∣[-2] S = ψI := by
  rw [ψS, ← slash_mul, S_mul_S_eq, slash_neg' _ _ (by decide), slash_one]

lemma ψS_slash_ST : ψS ∣[-2] (S * T) = ψT := by
  rw [slash_mul, ψS_slash_S, ψT]

lemma ψT_slash_T : ψT ∣[-2] T = ψI := by
  simp [-nsmul_eq_mul, ψT, ψI_eq, ← sub_eq_add_neg, div_sq_slash, H₂_T_action, H₃_T_action,
    H₄_T_action]

-- In my thesis, the - sign before ψS is missing. Makes no difference because we bound integrals in
-- absolute value, but point is that this way the Js look even more similar to the Is!
lemma ψS_slash_T : ψS ∣[-2] T = -ψS := by
  ext z
  simp [-nsmul_eq_mul, ψS, ψI_eq, div_sq_slash, H₂_S_action, H₃_S_action, H₄_S_action, H₂_T_action,
    H₃_T_action, H₄_T_action]
  ring

lemma ψT_slash_S : ψT ∣[-2] S = -ψT := by
  ext z
  simp [-nsmul_eq_mul, ψT, ψI_eq, div_sq_slash, H₂_S_action, H₃_S_action, H₄_S_action, H₂_T_action,
    H₃_T_action, H₄_T_action]
  ring

lemma ψI_slash_TS : ψI ∣[-2] (T * S) = -ψT := by
  rw [slash_mul, ← ψT, ψT_slash_S]

lemma ψS_slash_STS : ψS ∣[-2] (S * T * S) = -ψT := by
  rw [slash_mul, ψS_slash_ST, ψT_slash_S]

lemma ψS_slash_TSTS : ψS ∣[-2] (T * S * T * S) = ψT := by
  rw [slash_mul, slash_mul, slash_mul, ψS_slash_T, neg_slash, ψS_slash_S, neg_slash, ← ψT,
    neg_slash, ψT_slash_S, neg_neg]

/-- Translation by one on the upper half-plane exchanges `ψI` and `ψT`. -/
lemma ψI_T_smul (z : ℍ) : ψI (T • z) = ψT z := by
  rw [ψT, SL_slash_apply]
  simp [denom, ModularGroup.coe_T]

lemma ψT_T_smul (z : ℍ) : ψT (T • z) = ψI z := by
  rw [← congrFun ψT_slash_T z, SL_slash_apply]
  simp [denom, ModularGroup.coe_T]

/-- The translation relation used on the two shifted vertical contours. -/
lemma ψI'_add_one {z : ℂ} (hz : 0 < z.im) : ψI' (z + 1) = ψT' z := by
  have hz' : 0 < (z + 1).im := by simpa using hz
  rw [ψI'_def hz', ψT'_def hz, ← ψI_T_smul, modular_T_smul]
  congr 1
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_vadd, add_comm]

lemma ψI'_sub_one {z : ℂ} (hz : 0 < z.im) : ψI' (z - 1) = ψT' z := by
  have hz' : 0 < (z - 1).im := by simpa using hz
  rw [ψI'_def hz', ψT'_def hz]
  have h := ψT_T_smul (⟨z - 1, hz'⟩ : ℍ)
  have he : T • (⟨z - 1, hz'⟩ : ℍ) = ⟨z, hz⟩ := by
    rw [modular_T_smul]
    apply UpperHalfPlane.ext
    simp [UpperHalfPlane.coe_vadd, sub_eq_add_neg]
  simpa only [he] using h.symm

end rels

open MagicFunction.Parametrisations Set

section eq_of_mem

lemma ψI'_eq_ψI_of_mem {z : ℂ} (hz : 0 < z.im) : ψI' z = ψI ⟨z, hz⟩ := by simp [ψI', hz]

lemma ψS'_eq_ψS_of_mem {z : ℂ} (hz : 0 < z.im) : ψS' z = ψS ⟨z, hz⟩ := by simp [ψS', hz]

lemma ψT'_eq_ψT_of_mem {z : ℂ} (hz : 0 < z.im) : ψT' z = ψT ⟨z, hz⟩ := by simp [ψT', hz]

end eq_of_mem

section slash_explicit

lemma ψS_slash_ST_apply (z : ℍ) : (ψS ∣[-2] (S * T)) z = ψS' (-1 / (z + 1)) * (z + 1) ^ 2 := by
  rw [SL_slash_apply ψS (S * T) z, ← neg_inv_one_add_eq_ST z, ← ψS'_eq_ψS_of_mem]
  congr 1
  rw [denom]
  simp [SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

lemma ψS_slash_S_apply (z : ℍ) : (ψS ∣[-2] S) z = ψS' (-1 / z) * z ^ 2 := by
  rw [SL_slash_apply ψS S z, ← neg_inv_eq_S z, ← ψS'_eq_ψS_of_mem]
  congr 1
  rw [denom]
  simp [SpecialLinearGroup.map_apply_coe]

/-- `ψT` in terms of `ψS`, on `ℂ`: `ψT z = ψS (-1 / (z + 1)) (z + 1) ^ 2` for `z ∈ ℍ`. -/
lemma ψS_slash_ST_explicit {z : ℂ} (hz : 0 < z.im) :
    ψT' z = ψS' (-1 / (z + 1)) * (z + 1) ^ 2 := by
  rw [ψT'_eq_ψT_of_mem hz, ← ψS_slash_ST, ψS_slash_ST_apply]

/-- `ψI` in terms of `ψS`, on `ℂ`: `ψI z = ψS (-1 / z) z ^ 2` for `z ∈ ℍ`. -/
lemma ψS_slash_S_explicit {z : ℂ} (hz : 0 < z.im) : ψI' z = ψS' (-1 / z) * z ^ 2 := by
  rw [ψI'_eq_ψI_of_mem hz, ← ψS_slash_S, ψS_slash_S_apply]

end slash_explicit

section rels_explicit

/- The instances of the two previous lemmas along the contours `zᵢ'` used to define `b`. -/

lemma ψS_slash_ST_explicit₁ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψT' (z₁' t) = ψS' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₁'_pos ht)

lemma ψS_slash_ST_explicit₂ {t : ℝ} (ht : t ∈ Icc 0 1) :
    ψT' (z₂' t) = ψS' (-1 / (z₂' t + 1)) * (z₂' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₂'_pos ht)

lemma ψS_slash_ST_explicit₃ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψT' (z₃' t) = ψS' (-1 / (z₃' t + 1)) * (z₃' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₃'_pos ht)

lemma ψS_slash_ST_explicit₄ {t : ℝ} (ht : t ∈ Icc 0 1) :
    ψT' (z₄' t) = ψS' (-1 / (z₄' t + 1)) * (z₄' t + 1) ^ 2 :=
  ψS_slash_ST_explicit (im_z₄'_pos ht)

lemma ψS_slash_S_explicit₅ {t : ℝ} (ht : t ∈ Ioc 0 1) :
    ψI' (z₅' t) = ψS' (-1 / z₅' t) * (z₅' t) ^ 2 :=
  ψS_slash_S_explicit (im_z₅'_pos ht)

end rels_explicit
