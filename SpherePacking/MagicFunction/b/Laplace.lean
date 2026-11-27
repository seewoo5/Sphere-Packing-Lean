module

public import SpherePacking.MagicFunction.b.AnalyticContinuation

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Regularized Laplace formula for the radial profile of `b`
-/

@[expose] public section

open Set Filter MeasureTheory Real Complex MagicFunction.DoubleZeroes
open scoped Topology

namespace MagicFunction

private theorem ψI'_localIntegrable :
    LocallyIntegrableOn (fun t : ℝ ↦ ψI' (I * t)) (Ici 0) :=
  ψI'_imaginaryAxis_continuousOn.locallyIntegrableOn measurableSet_Ici

/-- Absolute convergence of the regularized integral in Proposition 7.45. -/
theorem integrableOn_regularized_b {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ ↦ (ψI' (I * t) - (cexp (2 * π * t) + 144)) *
      cexp (-π * s * t)) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ (ψI' (I * t) - (cexp (2 * π * t) + 144)) *
      cexp (-π * s * t)) (Ici 0) :=
    (ψI'_imaginaryAxis_continuousOn.sub (by fun_prop)).mul (by fun_prop)
  have hkernel : (fun t : ℝ ↦ cexp (-π * s * t)) =O[atTop] fun t ↦ rexp (-π * s * t) := by
    apply Asymptotics.isBigO_of_le
    intro t
    simp [Complex.norm_exp, Complex.mul_re]
  have hO := (ψI'_I_mul_sub_isBigO_atTop.mul hkernel).congr_right
    (g₂ := fun t ↦ rexp (-(π * (s + 1)) * t)) (fun t ↦ by rw [← Real.exp_add]; congr 1; ring)
  have hdecay : -(π * (s + 1)) < 0 := neg_lt_zero.mpr (mul_pos Real.pi_pos (by linarith))
  exact ((hcont.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop hO
    ⟨Ioi 0, Ioi_mem_atTop 0, integrableOn_exp_mul_Ioi hdecay 0⟩).mono_set Ioi_subset_Ici_self

/-- Proposition 7.45 away from the removable singularities, assuming analyticity of the
contour-defined radial profile on the positive axis. -/
theorem b_radial_eq_regularized_laplace
    (hb : AnalyticOnNhd ℝ b.RealIntegrals.b' (Ioi 0))
    {s : ℝ} (hs : 0 < s) (hs₂ : s ≠ 2) :
    b.RealIntegrals.b' s = -4 * I * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      (144 / (π * s) + 1 / (π * (s - 2)) +
        ∫ t in Ioi (0 : ℝ), (ψI' (I * t) - (cexp (2 * π * t) + 144)) * cexp (-π * s * t)) := by
  let R : ℂ → ℂ := fun z ↦ ∫ t in Ioi (0 : ℝ),
    (ψI' (I * t) - (cexp (2 * π * t) + 144)) * cexp (-π * z * t)
  let D : ℂ → ℂ := fun z ↦ π * z * (z - 2)
  let F : ℂ → ℂ := fun z ↦ -4 * I * (Complex.sin (π * z / 2)) ^ 2 *
    (144 * (z - 2) + z + D z * R z)
  have hR : AnalyticOnNhd ℂ R {z | -1 < z.re} := by
    simpa only [expPoly_ψI', neg_div, div_self Real.pi_ne_zero] using
      analyticOnNhd_integral_sub_expPoly Real.pi_pos ψI'_localIntegrable
        ψI'_I_mul_sub_expPoly_isBigO_atTop
  have hF : AnalyticOnNhd ℂ F {z | -1 < z.re} := by
    intro z hz
    have := hR z hz
    dsimp [F, D]
    fun_prop
  have hD : AnalyticOnNhd ℂ D univ := by
    intro z _
    dsimp [D]
    fun_prop
  have restrict_real (f : ℂ → ℂ) (U : Set ℂ) (hf : AnalyticOnNhd ℂ f U)
      (hU : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ U) :
      AnalyticOnNhd ℝ (fun x : ℝ ↦ f x) (Ioi 0) :=
    (hf.restrictScalars (𝕜 := ℝ)).comp (ofRealCLM.analyticOnNhd _) hU
  have hleft := (restrict_real D univ hD (by simp)).mul hb
  have hright := restrict_real F _ hF (by intro x hx; simpa using (by linarith : -1 < x))
  have hclear (x : ℝ) (hx : 0 < x) (hx₂ : x ≠ 2) :
      D x * (-4 * I * (Real.sin (π * x / 2) : ℂ) ^ 2 *
        (144 / (π * x) + 1 / (π * (x - 2)) + R x)) = F x := by
    have h₀ : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have h₂ : (x : ℂ) - 2 ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hx₂
    have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    dsimp [D, F]
    push_cast
    field_simp
  have hlarge (x : ℝ) (hx : 2 < x) : D x * b.RealIntegrals.b' x = F x := by
    have h := integral_eq_sum_add_integral_sub
      (s := (x : ℂ)) Real.pi_pos (by simpa using hx) ψI'_localIntegrable
      ψI'_I_mul_sub_expPoly_isBigO_atTop
    have he :
        (∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * x * t)) =
          144 / (π * x) + 1 / (π * (x - 2)) + R x := by
      simpa [Finset.sum_range_succ, R, add_comm] using h
    rw [b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral hx, he]
    exact hclear x (by linarith) (by linarith)
  have he := hleft.eqOn_of_preconnected_of_eventuallyEq hright isPreconnected_Ioi
    (show (3 : ℝ) ∈ Ioi 0 by norm_num)
    (by filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < 3 by norm_num)] with x hx
        exact hlarge x hx) hs
  have hDne : D s ≠ 0 := by
    simp only [D, mul_ne_zero_iff, ofReal_ne_zero, true_and]
    exact ⟨⟨Real.pi_ne_zero, hs.ne'⟩, by exact_mod_cast sub_ne_zero.mpr hs₂⟩
  exact mul_left_cancel₀ hDne (he.trans (hclear s hs hs₂).symm)

end MagicFunction
