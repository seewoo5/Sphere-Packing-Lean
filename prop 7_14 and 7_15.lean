import Mathlib

noncomputable section

open MeasureTheory
open scoped Interval

namespace Proposition714

def phi0H (z : UpperHalfPlane) : ℂ :=
  (EisensteinSeries.E2 z *
      (ModularForm.E₄ : UpperHalfPlane → ℂ) z -
    (ModularForm.E₆ : UpperHalfPlane → ℂ) z) ^ 2 /
      ModularForm.discriminant z

def phi0 (z : ℂ) : ℂ :=
  if hz : 0 < z.im then phi0H ⟨z, hz⟩ else 0

def segmentIntegral (f : ℂ → ℂ) (p q : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1,
    f (p + (t : ℂ) * (q - p)) * (q - p)

def verticalRayIntegral (f : ℂ → ℂ) (y : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi y,
    f (Complex.I * (t : ℂ)) * Complex.I

def gaussian (s : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (s : ℂ) * z)

def inversionKernel (z : ℂ) : ℂ :=
  phi0 (-1 / z) * z ^ 2

def aRad (s : ℝ) : ℂ :=
  let left : ℂ → ℂ :=
    fun z => inversionKernel (z + 1) * gaussian s z
  let right : ℂ → ℂ :=
    fun z => inversionKernel (z - 1) * gaussian s z
  let middle : ℂ → ℂ :=
    fun z => inversionKernel z * gaussian s z
  segmentIntegral left (-1) (-1 + Complex.I) +
    segmentIntegral left (-1 + Complex.I) Complex.I +
    segmentIntegral right 1 (1 + Complex.I) +
    segmentIntegral right (1 + Complex.I) Complex.I -
    2 * segmentIntegral middle 0 Complex.I +
    2 * verticalRayIntegral
      (fun z => phi0 z * gaussian s z) 1

def laplaceIntegrand (r t : ℝ) : ℂ :=
  phi0 (Complex.I / (t : ℂ)) * (t : ℂ) ^ 2 *
    (Real.exp (-Real.pi * r ^ 2 * t) : ℂ)


theorem Proposition7_14_laplace :
    ∀ r : ℝ, Real.sqrt 2 < r →
      IntegrableOn
        (laplaceIntegrand r)
        (Set.Ioi (0 : ℝ)) ∧
      aRad (r ^ 2) =
        4 * Complex.I *
          (Real.sin (Real.pi * r ^ 2 / 2) : ℂ) ^ 2 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            laplaceIntegrand r t) := by
  sorry

end Proposition714

end

noncomputable section

open MeasureTheory

namespace Proposition715

def regularizedIntegrand (r t : ℝ) : ℂ :=
  Proposition714.laplaceIntegrand r t -
    Complex.ofReal
      (36 / Real.pi ^ 2 * Real.exp (2 * Real.pi * t)
        - 8640 / Real.pi * t + 18144 / Real.pi ^ 2) *
      Complex.ofReal (Real.exp (-Real.pi * r ^ 2 * t))


def regularizedRHS (r : ℝ) : ℂ :=
  let s : ℝ := r ^ 2
  let x : ℝ := Real.pi * s / 2
  let y : ℝ := x - Real.pi
  (Complex.I / (Real.pi : ℂ)) *
      Complex.ofReal
        (36 * (s - 2) * (Real.sinc y) ^ 2
          + (18144 * s - 8640) * (Real.sinc x) ^ 2)
    + (4 : ℂ) * Complex.I * (Real.sin x : ℂ) ^ 2 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          regularizedIntegrand r t)


theorem Proposition7_15 :
  ∀ r : ℝ, 0 ≤ r →
    IntegrableOn (regularizedIntegrand r) (Set.Ioi (0 : ℝ)) ∧
    Proposition714.aRad (r ^ 2) = regularizedRHS r := by sorry

end Proposition715

end
