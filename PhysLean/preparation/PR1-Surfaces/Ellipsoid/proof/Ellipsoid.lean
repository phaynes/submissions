/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalShell
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
/-!

## Ellipsoid surface in `Space 3`

This file defines the diagonal ellipsoid parametrization in `Space 3`, obtained by
scaling the unit sphere coordinatewise. The associated measure is the pushforward of
the sphere measure weighted by the usual diagonal-linear-map surface density
`|∏ᵢ aᵢ| * √(∑ᵢ (uᵢ / aᵢ)^2)`.

This is a parametrized surface measure. It does not assert equality with intrinsic
Hausdorff measure.

-/

@[expose] public section
open SchwartzMap NNReal
open scoped BigOperators
noncomputable section
open Physlib Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the ellipsoid surface

-/

/-- The parameter space for the diagonal ellipsoid: the unit sphere in `Space 3`. -/
abbrev EllipsoidParameter := Metric.sphere (0 : Space 3) 1

/-- The diagonal ellipsoid parametrization in `Space 3`. -/
def ellipsoid (a : Fin 3 → ℝ) : EllipsoidParameter → Space 3 := fun x =>
  ⟨fun i => a i * (sphericalShell 3 x) i⟩

@[fun_prop]
lemma ellipsoid_continuous (a : Fin 3 → ℝ) : Continuous (ellipsoid a) := by
  change Continuous ((fun f : Fin 3 → ℝ => (⟨f⟩ : Space 3)) ∘
    (fun x : EllipsoidParameter => fun i => a i * (sphericalShell 3 x) i))
  exact Space.mk_continuous.comp (by fun_prop)

/-!

## B. The measure associated with the ellipsoid

-/

/-- The real-valued Jacobian density for the diagonal ellipsoid parametrization. -/
def ellipsoidDensity (a : Fin 3 → ℝ) : EllipsoidParameter → ℝ := fun x =>
  |∏ i, a i| * √(∑ i, (((sphericalShell 3 x) i) / a i) ^ 2)

/-- The nonnegative Jacobian density for the diagonal ellipsoid parametrization. -/
def ellipsoidDensityNNReal (a : Fin 3 → ℝ) : EllipsoidParameter → ℝ≥0 := fun x =>
  Real.toNNReal (ellipsoidDensity a x)

lemma ellipsoidDensity_nonneg (a : Fin 3 → ℝ) (x : EllipsoidParameter) :
    0 ≤ ellipsoidDensity a x := by
  unfold ellipsoidDensity
  positivity

@[fun_prop]
lemma ellipsoidDensity_continuous (a : Fin 3 → ℝ) : Continuous (ellipsoidDensity a) := by
  unfold ellipsoidDensity
  fun_prop

@[fun_prop]
lemma ellipsoidDensityNNReal_continuous (a : Fin 3 → ℝ) :
    Continuous (ellipsoidDensityNNReal a) := by
  unfold ellipsoidDensityNNReal
  fun_prop

lemma ellipsoidDensityNNReal_coe (a : Fin 3 → ℝ) (x : EllipsoidParameter) :
    (ellipsoidDensityNNReal a x : ℝ) = ellipsoidDensity a x := by
  rw [ellipsoidDensityNNReal, Real.coe_toNNReal _ (ellipsoidDensity_nonneg a x)]

lemma ellipsoidDensity_integrable (a : Fin 3 → ℝ) :
    Integrable (ellipsoidDensity a) (MeasureTheory.Measure.toSphere volume) := by
  let f' : BoundedContinuousFunction EllipsoidParameter ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨ellipsoidDensity a, ellipsoidDensity_continuous a⟩
  exact BoundedContinuousFunction.integrable _ f'

/-- The weighted parameter-space measure for the diagonal ellipsoid. -/
def ellipsoidParameterMeasure (a : Fin 3 → ℝ) : Measure EllipsoidParameter :=
  (MeasureTheory.Measure.toSphere volume).withDensity fun x => ellipsoidDensityNNReal a x

instance ellipsoidParameterMeasure_finite (a : Fin 3 → ℝ) :
    IsFiniteMeasure (ellipsoidParameterMeasure a) := by
  rw [ellipsoidParameterMeasure]
  convert isFiniteMeasure_withDensity_ofReal (ellipsoidDensity_integrable a).2 using 2
  ext x
  rfl

/-- The measure on `Space 3` corresponding to integration over a diagonal ellipsoid. -/
def ellipsoidMeasure (a : Fin 3 → ℝ) : Measure (Space 3) :=
  MeasureTheory.Measure.map (ellipsoid a) (ellipsoidParameterMeasure a)

instance ellipsoidMeasure_finite (a : Fin 3 → ℝ) : IsFiniteMeasure (ellipsoidMeasure a) := by
  rw [ellipsoidMeasure]
  exact Measure.isFiniteMeasure_map (ellipsoidParameterMeasure a) (ellipsoid a)

instance ellipsoidMeasure_hasTemperateGrowth (a : Fin 3 → ℝ) :
    (ellipsoidMeasure a).HasTemperateGrowth := by
  refine { exists_integrable := ?_ }
  use 0
  simp

instance ellipsoidMeasure_sFinite (a : Fin 3 → ℝ) : SFinite (ellipsoidMeasure a) := by
  infer_instance

/-!

## C. The distribution associated with the ellipsoid

-/

/-- The distribution on `Space 3` corresponding to integration over a diagonal ellipsoid. -/
def ellipsoidDist (a : Fin 3 → ℝ) : (Space 3) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ (ellipsoidMeasure a)

lemma ellipsoidDist_apply_eq_integral_ellipsoidMeasure
    (a : Fin 3 → ℝ) (f : 𝓢(Space 3, ℝ)) :
    ellipsoidDist a f = ∫ x, f x ∂ellipsoidMeasure a := by
  rw [ellipsoidDist, SchwartzMap.integralCLM_apply]

lemma ellipsoidDist_apply_eq_integral_parameterMeasure
    (a : Fin 3 → ℝ) (f : 𝓢(Space 3, ℝ)) :
    ellipsoidDist a f = ∫ x, f (ellipsoid a x) ∂ellipsoidParameterMeasure a := by
  rw [ellipsoidDist_apply_eq_integral_ellipsoidMeasure, ellipsoidMeasure]
  rw [integral_map]
  · exact (ellipsoid_continuous a).aemeasurable
  · fun_prop

lemma ellipsoidDist_apply_eq_integral_density (a : Fin 3 → ℝ) (f : 𝓢(Space 3, ℝ)) :
    ellipsoidDist a f =
      ∫ x, ellipsoidDensity a x * f (ellipsoid a x)
        ∂(MeasureTheory.Measure.toSphere volume) := by
  rw [ellipsoidDist_apply_eq_integral_parameterMeasure, ellipsoidParameterMeasure]
  rw [integral_withDensity_eq_integral_smul (ellipsoidDensityNNReal_continuous a).measurable]
  congr
  funext x
  rw [NNReal.smul_def, ellipsoidDensityNNReal_coe]
  simp [smul_eq_mul]

end Space
