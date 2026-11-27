module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import SpherePacking.MagicFunction.a.Schwartz

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Analytic continuation of `a`

Integral representations and regularization of Viazovska's function `a`.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory Real Complex
open scoped Topology

namespace MagicFunction

/-- The remainder estimate used in Proposition 7.21, equation (47). -/
theorem φ₀''_I_div_mul_sq_sub_isBigO_atTop :
    (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2 -
      (36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2)) =O[atTop]
        fun t ↦ t ^ 2 * rexp (-2 * π * t) := by
  sorry

theorem neg_sq_mul_φ₀''_neg_inv_I_mul (t : ℝ) :
    -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) = φ₀'' (I / t) * t ^ 2 := by
  have h : -1 / (I * t) = I / t := by
    simp [div_eq_mul_inv, Complex.inv_I, mul_comm]
  rw [h, mul_pow, I_sq]
  ring

end MagicFunction

namespace MagicFunction.a.AnalyticContinuation

def laplaceIntegrand (r t : ℝ) : ℂ :=
  φ₀'' (I / (t : ℂ)) * (t : ℂ) ^ 2 *
    cexp ((-π * r * t : ℝ) : ℂ)

def modelIntegrand (r t : ℝ) : ℂ :=
  ((36 / π ^ 2 * Real.exp (2 * π * t) -
      8640 / π * t + 18144 / π ^ 2 : ℝ) : ℂ) *
    cexp ((-π * r * t : ℝ) : ℂ)

def regularizedIntegrand (r t : ℝ) : ℂ :=
  laplaceIntegrand r t - modelIntegrand r t

def regularizedRHS (r : ℝ) : ℂ :=
  let u : ℝ := π * r / 2
  (I / (π : ℂ)) *
      ((36 * (r - 2) * (Real.sinc (u - π)) ^ 2 +
          (18144 * r - 8640) * (Real.sinc u) ^ 2 : ℝ) : ℂ) +
    4 * I * (Real.sin u : ℂ) ^ 2 *
      (∫ t : ℝ in Ioi (0 : ℝ), regularizedIntegrand r t)

/-! The sinc factor really is analytic, including at its removable singularity. -/

theorem analyticAt_sinc_aux (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  rw [Real.sinc_eq_dslope]
  exact Real.analyticAt_sin.dslope 0

theorem sinc_prefactor_identity {r : ℝ} (hr0 : r ≠ 0) (hr2 : r ≠ 2) :
    (36 * (r - 2) * Real.sinc (π * r / 2 - π) ^ 2 +
        (18144 * r - 8640) * Real.sinc (π * r / 2) ^ 2) / π =
      4 * Real.sin (π * r / 2) ^ 2 *
        (36 / (π ^ 3 * (r - 2)) - 8640 / (π ^ 3 * r ^ 2) +
          18144 / (π ^ 3 * r)) := by
  have hu : π * r / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero Real.pi_ne_zero hr0) (by norm_num)
  have hd : r - 2 ≠ 0 := sub_ne_zero.mpr hr2
  have hshift : π * r / 2 - π = π * (r - 2) / 2 := by ring
  have hv : π * r / 2 - π ≠ 0 := by
    rw [hshift]
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hd) (by norm_num)
  rw [Real.sinc_of_ne_zero hv, Real.sinc_of_ne_zero hu, Real.sin_sub_pi,
    hshift]
  field_simp [Real.pi_ne_zero, hr0, hd]
  ring

theorem sinc_prefactor_identity_complex {r : ℝ} (hr0 : r ≠ 0) (hr2 : r ≠ 2) :
    (I / (π : ℂ)) *
        ((36 * (r - 2) * Real.sinc (π * r / 2 - π) ^ 2 +
            (18144 * r - 8640) * Real.sinc (π * r / 2) ^ 2 : ℝ) : ℂ) =
      4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
        ((36 / (π ^ 3 * (r - 2)) - 8640 / (π ^ 3 * r ^ 2) +
          18144 / (π ^ 3 * r) : ℝ) : ℂ) := by
  have h := congrArg (fun y : ℝ => (y : ℂ))
    (sinc_prefactor_identity hr0 hr2)
  push_cast at h
  calc
    _ = I *
        (((36 * (r - 2) * Real.sinc (π * r / 2 - π) ^ 2 +
            (18144 * r - 8640) * Real.sinc (π * r / 2) ^ 2 : ℝ) : ℂ) /
          (π : ℂ)) := by ring
    _ = _ := by
      push_cast
      rw [h]
      ring

/-! The elementary model can be integrated without any modular-form hypotheses. -/

def decayKernel (c t : ℝ) : ℂ := cexp (-(c : ℂ) * (t : ℂ))

theorem integrableOn_decayKernel {c : ℝ} (hc : 0 < c) :
    IntegrableOn (decayKernel c) (Ioi (0 : ℝ)) := by
  have hneg : (-(c : ℂ)).re < 0 := by
    simpa using (show -c < 0 by linarith)
  change IntegrableOn (fun t : ℝ => cexp (-(c : ℂ) * (t : ℂ))) (Ioi (0 : ℝ))
  exact integrableOn_exp_mul_complex_Ioi (a := -(c : ℂ)) hneg 0

theorem integral_decayKernel {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi (0 : ℝ), decayKernel c t) = 1 / (c : ℂ) := by
  have hneg : (-(c : ℂ)).re < 0 := by
    simpa using (show -c < 0 by linarith)
  simpa only [decayKernel, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    neg_div_neg_eq] using
      integral_exp_mul_complex_Ioi (a := -(c : ℂ)) hneg (0 : ℝ)

theorem integral_mul_decayKernel {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) * decayKernel c t) =
      (1 / (c : ℂ)) ^ 2 := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℂ)) (r := c) (by norm_num) hc
  norm_num at h
  simpa [decayKernel, neg_mul] using h

theorem integrableOn_mul_decayKernel {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * decayKernel c t) (Ioi (0 : ℝ)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_mul_decayKernel hc]
  exact pow_ne_zero 2 (one_div_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'))

theorem modelIntegrand_eq (r t : ℝ) :
    modelIntegrand r t =
      (36 / (π : ℂ) ^ 2) * decayKernel (π * (r - 2)) t -
        (8640 / (π : ℂ)) * ((t : ℂ) * decayKernel (π * r) t) +
        (18144 / (π : ℂ) ^ 2) * decayKernel (π * r) t := by
  have hk : cexp ((-π * r * t : ℝ) : ℂ) = decayKernel (π * r) t := by
    unfold decayKernel
    congr 1
    push_cast
    ring
  have he : ((Real.exp (2 * π * t) : ℝ) : ℂ) * decayKernel (π * r) t =
      decayKernel (π * (r - 2)) t := by
    rw [Complex.ofReal_exp]
    unfold decayKernel
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold modelIntegrand
  rw [hk]
  push_cast
  push_cast at he
  rw [← he]
  ring

theorem integrableOn_modelIntegrand {r : ℝ} (hr : 2 < r) :
    IntegrableOn (modelIntegrand r) (Ioi (0 : ℝ)) := by
  have hp : 0 < π * r := mul_pos Real.pi_pos (by linarith)
  have hd : 0 < π * (r - 2) := mul_pos Real.pi_pos (by linarith)
  change IntegrableOn (fun t => modelIntegrand r t) (Ioi (0 : ℝ))
  simp_rw [modelIntegrand_eq]
  exact (((integrableOn_decayKernel hd).const_mul (36 / (π : ℂ) ^ 2)).sub
    ((integrableOn_mul_decayKernel hp).const_mul (8640 / (π : ℂ)))).add
      ((integrableOn_decayKernel hp).const_mul (18144 / (π : ℂ) ^ 2))

theorem integral_modelIntegrand {r : ℝ} (hr : 2 < r) :
    (∫ t : ℝ in Ioi (0 : ℝ), modelIntegrand r t) =
      ((36 / (π ^ 3 * (r - 2)) - 8640 / (π ^ 3 * r ^ 2) +
        18144 / (π ^ 3 * r) : ℝ) : ℂ) := by
  have hp : 0 < π * r := mul_pos Real.pi_pos (by linarith)
  have hd : 0 < π * (r - 2) := mul_pos Real.pi_pos (by linarith)
  let f : ℝ → ℂ := fun t => (36 / (π : ℂ) ^ 2) * decayKernel (π * (r - 2)) t
  let g : ℝ → ℂ := fun t => (8640 / (π : ℂ)) * ((t : ℂ) * decayKernel (π * r) t)
  let h : ℝ → ℂ := fun t => (18144 / (π : ℂ) ^ 2) * decayKernel (π * r) t
  have hf : IntegrableOn f (Ioi (0 : ℝ)) :=
    (integrableOn_decayKernel hd).const_mul (36 / (π : ℂ) ^ 2)
  have hg : IntegrableOn g (Ioi (0 : ℝ)) :=
    (integrableOn_mul_decayKernel hp).const_mul (8640 / (π : ℂ))
  have hh : IntegrableOn h (Ioi (0 : ℝ)) :=
    (integrableOn_decayKernel hp).const_mul (18144 / (π : ℂ) ^ 2)
  have hsplit : (∫ t : ℝ in Ioi (0 : ℝ), modelIntegrand r t) =
      ((∫ t : ℝ in Ioi (0 : ℝ), f t) -
        (∫ t : ℝ in Ioi (0 : ℝ), g t)) +
          (∫ t : ℝ in Ioi (0 : ℝ), h t) := by
    calc
      _ = ∫ t : ℝ in Ioi (0 : ℝ), f t - g t + h t := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => modelIntegrand_eq r t)
      _ = (∫ t : ℝ in Ioi (0 : ℝ), f t - g t) +
          (∫ t : ℝ in Ioi (0 : ℝ), h t) := integral_add (hf.sub hg) hh
      _ = _ := congrArg (fun z : ℂ => z + ∫ t : ℝ in Ioi (0 : ℝ), h t)
        (integral_sub hf hg)
  rw [hsplit]
  dsimp only [f, g, h]
  simp only [integral_const_mul, integral_decayKernel hd,
    integral_mul_decayKernel hp, integral_decayKernel hp]
  have hp0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hr2 : (r : ℂ) - 2 ≠ 0 := by
    exact_mod_cast (show r - 2 ≠ 0 by linarith)
  push_cast
  field_simp [hp0, hr0, hr2]

/-! Reduction of regularized integrability to the single parameter `r = 0`. -/

theorem regularizedIntegrand_eq_mul_zero (r t : ℝ) :
    regularizedIntegrand r t =
      regularizedIntegrand 0 t * cexp ((-π * r * t : ℝ) : ℂ) := by
  simp only [regularizedIntegrand, modelIntegrand, laplaceIntegrand,
    mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  ring

theorem integrableOn_regularizedIntegrand_of_zero
    (hzero : IntegrableOn (regularizedIntegrand 0) (Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (regularizedIntegrand r) (Ioi (0 : ℝ)) := by
  have heq : regularizedIntegrand r = fun t =>
      regularizedIntegrand 0 t * cexp ((-π * r * t : ℝ) : ℂ) :=
    funext (regularizedIntegrand_eq_mul_zero r)
  rw [heq]
  have hc : Continuous (fun t : ℝ => cexp ((-π * r * t : ℝ) : ℂ)) :=
    Complex.continuous_exp.comp
      (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))
  refine hzero.norm.mono'
    (hzero.aestronglyMeasurable.mul hc.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  apply Real.exp_le_one_iff.mpr
  have hnonneg : 0 ≤ π * r * t :=
    mul_nonneg (mul_nonneg Real.pi_pos.le hr) (le_of_lt ht)
  simpa only [neg_mul] using neg_nonpos.mpr hnonneg

theorem integrableOn_laplaceIntegrand_of_regularized
    {r : ℝ} (hr : 2 < r)
    (hreg : IntegrableOn (regularizedIntegrand r) (Ioi (0 : ℝ))) :
    IntegrableOn (laplaceIntegrand r) (Ioi (0 : ℝ)) := by
  apply (hreg.add (integrableOn_modelIntegrand hr)).congr
  exact Filter.Eventually.of_forall (fun t => by simp [regularizedIntegrand])

/-! The remaining analytic results from Propositions 7.20 and 7.21. -/

/-- Absolute convergence of the regularized integral in Proposition 7.21. -/
theorem integrableOn_regularizedIntegrand {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (regularizedIntegrand r) (Ioi (0 : ℝ)) := by
  sorry

/-- Absolute convergence of the Laplace integral in Proposition 7.20. -/
theorem integrableOn_φ₀''_mul_sq_mul_cexp {r : ℝ} (hr : 2 < r) :
    IntegrableOn (laplaceIntegrand r) (Ioi (0 : ℝ)) := by
  exact integrableOn_laplaceIntegrand_of_regularized hr
    (integrableOn_regularizedIntegrand (by linarith))

/-- Proposition 7.20, with `r` the squared radius. -/
theorem a'_eq_four_mul_I_mul_sin_sq_mul_integral {r : ℝ} (hr : 2 < r) :
    MagicFunction.a.RealIntegrals.a' r =
      4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
        (∫ t : ℝ in Ioi (0 : ℝ), laplaceIntegrand r t) := by
  sorry

theorem a_eq_four_mul_I_mul_sin_sq_mul_integral
    {x : EuclideanSpace ℝ (Fin 8)} (hx : √2 < ‖x‖) :
    MagicFunction.FourierEigenfunctions.a x =
      4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
        (∫ t : ℝ in Ioi (0 : ℝ), laplaceIntegrand (‖x‖ ^ 2) t) := by
  rw [MagicFunction.FourierEigenfunctions.a_apply]
  exact a'_eq_four_mul_I_mul_sin_sq_mul_integral (Real.lt_sq_of_sqrt_lt hx)

/-! This assembly theorem assumes the still-needed Proposition 7.20 identity. -/

theorem a'_eq_regularizedRHS_of_gt_two
    {r : ℝ} (hr : 2 < r)
    (hreg : IntegrableOn (regularizedIntegrand r) (Ioi (0 : ℝ)))
    (h20 : MagicFunction.a.RealIntegrals.a' r =
      4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
        (∫ t : ℝ in Ioi (0 : ℝ), laplaceIntegrand r t)) :
    MagicFunction.a.RealIntegrals.a' r = regularizedRHS r := by
  have hi : (∫ t : ℝ in Ioi (0 : ℝ), laplaceIntegrand r t) =
      (∫ t : ℝ in Ioi (0 : ℝ), regularizedIntegrand r t) +
        (∫ t : ℝ in Ioi (0 : ℝ), modelIntegrand r t) := by
    calc
      _ = ∫ t : ℝ in Ioi (0 : ℝ),
          regularizedIntegrand r t + modelIntegrand r t := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by simp [regularizedIntegrand])
      _ = _ := integral_add hreg (integrableOn_modelIntegrand hr)
  unfold regularizedRHS
  dsimp only
  rw [h20, hi, integral_modelIntegrand hr, mul_add]
  rw [← sinc_prefactor_identity_complex (by linarith : r ≠ 0)
    (by linarith : r ≠ 2)]
  exact add_comm _ _

/-!
The identity-principle step is a real-analytic one. Equality on the open
interval `(2, ∞)` supplies equality in a real neighborhood of `3`.
-/

theorem a'_eq_regularizedRHS_of_analytic_inputs
    (hreg0 : IntegrableOn (regularizedIntegrand 0) (Ioi (0 : ℝ)))
    (h20 : ∀ r : ℝ, 2 < r →
      MagicFunction.a.RealIntegrals.a' r =
        4 * I * (Real.sin (π * r / 2) : ℂ) ^ 2 *
          (∫ t : ℝ in Ioi (0 : ℝ), laplaceIntegrand r t))
    (ha : AnalyticOnNhd ℝ MagicFunction.a.RealIntegrals.a' (Ioi (-2 : ℝ)))
    (hR : AnalyticOnNhd ℝ regularizedRHS (Ioi (-2 : ℝ)))
    {r : ℝ} (hr : 0 ≤ r) :
    MagicFunction.a.RealIntegrals.a' r = regularizedRHS r := by
  have he : MagicFunction.a.RealIntegrals.a' =ᶠ[𝓝 (3 : ℝ)] regularizedRHS := by
    filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < 3 by norm_num)] with s hs
    change (2 : ℝ) < s at hs
    have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 2) hs.le
    exact a'_eq_regularizedRHS_of_gt_two hs
      (integrableOn_regularizedIntegrand_of_zero hreg0 hs0) (h20 s hs)
  have hEq : EqOn MagicFunction.a.RealIntegrals.a' regularizedRHS (Ioi (-2 : ℝ)) :=
    ha.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_Ioi
      (by norm_num : (3 : ℝ) ∈ Ioi (-2 : ℝ)) he
  exact hEq (by change -2 < r; linarith)

/-- Proposition 7.21 after filling in the missing analytic estimates. -/
theorem a'_eq_regularizedRHS {r : ℝ} (hr : 0 ≤ r) :
    MagicFunction.a.RealIntegrals.a' r = regularizedRHS r := by
  sorry

theorem a_eq_regularizedRHS (x : EuclideanSpace ℝ (Fin 8)) :
    MagicFunction.FourierEigenfunctions.a x = regularizedRHS (‖x‖ ^ 2) := by
  rw [MagicFunction.FourierEigenfunctions.a_apply]
  exact a'_eq_regularizedRHS (sq_nonneg ‖x‖)

theorem regularizedRHS_zero : regularizedRHS 0 = -8640 * I / (π : ℂ) := by
  simp [regularizedRHS, Real.sinc_of_ne_zero Real.pi_ne_zero]
  ring

theorem regularizedRHS_two : regularizedRHS 2 = 0 := by
  have hu : π * (2 : ℝ) / 2 = π := by ring
  simp [regularizedRHS, hu, Real.sinc_of_ne_zero Real.pi_ne_zero]

end MagicFunction.a.AnalyticContinuation

end -- noncomputable section

end -- public section
