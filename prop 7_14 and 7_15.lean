
module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import SpherePacking.MagicFunction.a.Schwartz

@[expose] public section

noncomputable section

open Set MeasureTheory Real Complex

namespace MagicFunction.a.AnalyticContinuation

def laplaceIntegrand (r t : ℝ) : ℂ :=
  φ₀'' (I / (t : ℂ)) * (t : ℂ) ^ 2 *
    cexp ((-π * r * t : ℝ) : ℂ)


theorem integrableOn_φ₀''_mul_sq_mul_cexp {r : ℝ} (hr : 2 < r) :
    IntegrableOn (laplaceIntegrand r) (Ioi (0 : ℝ)) := by
  sorry


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
  exact a'_eq_four_mul_I_mul_sin_sq_mul_integral
    (Real.lt_sq_of_sqrt_lt hx)


def regularizedIntegrand (r t : ℝ) : ℂ :=
  laplaceIntegrand r t -
    ((36 / π ^ 2 * Real.exp (2 * π * t) -
        8640 / π * t + 18144 / π ^ 2 : ℝ) : ℂ) *
      cexp ((-π * r * t : ℝ) : ℂ)


def regularizedRHS (r : ℝ) : ℂ :=
  let u : ℝ := π * r / 2
  (I / (π : ℂ)) *
      ((36 * (r - 2) * (Real.sinc (u - π)) ^ 2 +
          (18144 * r - 8640) * (Real.sinc u) ^ 2 : ℝ) : ℂ) +
    4 * I * (Real.sin u : ℂ) ^ 2 *
      (∫ t : ℝ in Ioi (0 : ℝ), regularizedIntegrand r t)


theorem integrableOn_regularizedIntegrand {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (regularizedIntegrand r) (Ioi (0 : ℝ)) := by
  sorry


theorem a'_eq_regularizedRHS {r : ℝ} (hr : 0 ≤ r) :
    MagicFunction.a.RealIntegrals.a' r = regularizedRHS r := by
  sorry


theorem a_eq_regularizedRHS (x : EuclideanSpace ℝ (Fin 8)) :
    MagicFunction.FourierEigenfunctions.a x = regularizedRHS (‖x‖ ^ 2) := by
  rw [MagicFunction.FourierEigenfunctions.a_apply]
  exact a'_eq_regularizedRHS (sq_nonneg ‖x‖)

end MagicFunction.a.AnalyticContinuation

end

