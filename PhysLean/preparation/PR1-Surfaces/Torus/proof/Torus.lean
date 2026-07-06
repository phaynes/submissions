/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalCylinder
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
/-!

## Torus surface in `Space 3`

This file defines the standard torus parametrization in `Space 3`. The first circle is
the major-angle parameter and the second circle is the meridian-angle parameter. The
associated measure is the pushforward of the product circle measure weighted by the
Jacobian density `|r| * |R + r * cos θ|`.

This is a parametrized surface measure. It does not assert equality with intrinsic
Hausdorff measure, and the parametrization is not asserted to be injective for all
parameters.

-/

@[expose] public section
open SchwartzMap NNReal
noncomputable section
open Physlib Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the torus surface

-/

/-- The parameter space for a torus: a product of two unit circles. -/
abbrev TorusParameter := Metric.sphere (0 : Space 2) 1 × Metric.sphere (0 : Space 2) 1

/-- The torus parametrization in `Space 3`.

For parameters `(u, v)` on two unit circles, `u` gives the major-angle direction and `v`
gives the meridian direction. The point has transverse component
`(R + r * v₀) • u` and axial component `r * v₁`. -/
def torus (R r : ℝ) : TorusParameter → Space 3 := fun x =>
  (slice 2).symm
    (r * (sphericalShell 2 x.2) 1,
      (R + r * (sphericalShell 2 x.2) 0) • sphericalShell 2 x.1)

lemma torus_eq (R r : ℝ) :
    torus R r = (slice 2).symm ∘ (fun x : TorusParameter =>
      (r * (sphericalShell 2 x.2) 1,
        (R + r * (sphericalShell 2 x.2) 0) • sphericalShell 2 x.1)) := rfl

@[fun_prop]
lemma torus_continuous (R r : ℝ) : Continuous (torus R r) := by
  rw [torus_eq]
  fun_prop

/-!

## B. The measure associated with the torus

-/

/-- The real-valued Jacobian density for the torus parametrization. -/
def torusDensity (R r : ℝ) : TorusParameter → ℝ := fun x =>
  |r| * |R + r * (sphericalShell 2 x.2) 0|

/-- The nonnegative Jacobian density for the torus parametrization. -/
def torusDensityNNReal (R r : ℝ) : TorusParameter → ℝ≥0 := fun x =>
  Real.toNNReal (torusDensity R r x)

lemma torusDensity_nonneg (R r : ℝ) (x : TorusParameter) : 0 ≤ torusDensity R r x := by
  unfold torusDensity
  positivity

@[fun_prop]
lemma torusDensity_continuous (R r : ℝ) : Continuous (torusDensity R r) := by
  unfold torusDensity
  fun_prop

@[fun_prop]
lemma torusDensityNNReal_continuous (R r : ℝ) : Continuous (torusDensityNNReal R r) := by
  unfold torusDensityNNReal
  fun_prop

lemma torusDensityNNReal_coe (R r : ℝ) (x : TorusParameter) :
    (torusDensityNNReal R r x : ℝ) = torusDensity R r x := by
  rw [torusDensityNNReal, Real.coe_toNNReal _ (torusDensity_nonneg R r x)]

lemma torusDensity_integrable (R r : ℝ) :
    Integrable (torusDensity R r)
      ((MeasureTheory.Measure.toSphere volume).prod (MeasureTheory.Measure.toSphere volume)) := by
  let f' : BoundedContinuousFunction TorusParameter ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨torusDensity R r, torusDensity_continuous R r⟩
  exact BoundedContinuousFunction.integrable _ f'

/-- The weighted parameter-space measure for the torus. -/
def torusParameterMeasure (R r : ℝ) : Measure TorusParameter :=
  ((MeasureTheory.Measure.toSphere volume).prod
      (MeasureTheory.Measure.toSphere volume)).withDensity
    fun x => torusDensityNNReal R r x

instance torusParameterMeasure_finite (R r : ℝ) :
    IsFiniteMeasure (torusParameterMeasure R r) := by
  rw [torusParameterMeasure]
  convert isFiniteMeasure_withDensity_ofReal (torusDensity_integrable R r).2 using 2
  ext x
  rfl

/-- The measure on `Space 3` corresponding to integration over a torus. -/
def torusMeasure (R r : ℝ) : Measure (Space 3) :=
  MeasureTheory.Measure.map (torus R r) (torusParameterMeasure R r)

instance torusMeasure_finite (R r : ℝ) : IsFiniteMeasure (torusMeasure R r) := by
  rw [torusMeasure]
  exact Measure.isFiniteMeasure_map (torusParameterMeasure R r) (torus R r)

instance torusMeasure_hasTemperateGrowth (R r : ℝ) :
    (torusMeasure R r).HasTemperateGrowth := by
  refine { exists_integrable := ?_ }
  use 0
  simp

instance torusMeasure_sFinite (R r : ℝ) : SFinite (torusMeasure R r) := by
  infer_instance

/-!

## C. The distribution associated with the torus

-/

/-- The distribution on `Space 3` corresponding to integration over a torus. -/
def torusDist (R r : ℝ) : (Space 3) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ (torusMeasure R r)

lemma torusDist_apply_eq_integral_torusMeasure (R r : ℝ) (f : 𝓢(Space 3, ℝ)) :
    torusDist R r f = ∫ x, f x ∂torusMeasure R r := by
  rw [torusDist, SchwartzMap.integralCLM_apply]

lemma torusDist_apply_eq_integral_parameterMeasure (R r : ℝ) (f : 𝓢(Space 3, ℝ)) :
    torusDist R r f = ∫ x, f (torus R r x) ∂torusParameterMeasure R r := by
  rw [torusDist_apply_eq_integral_torusMeasure, torusMeasure]
  rw [integral_map]
  · exact (torus_continuous R r).aemeasurable
  · fun_prop

lemma torusDist_apply_eq_integral_density (R r : ℝ) (f : 𝓢(Space 3, ℝ)) :
    torusDist R r f =
      ∫ x, torusDensity R r x * f (torus R r x)
        ∂(((MeasureTheory.Measure.toSphere volume).prod
          (MeasureTheory.Measure.toSphere volume))) := by
  rw [torusDist_apply_eq_integral_parameterMeasure, torusParameterMeasure]
  rw [integral_withDensity_eq_integral_smul (torusDensityNNReal_continuous R r).measurable]
  congr
  funext x
  rw [NNReal.smul_def, torusDensityNNReal_coe]
  simp [smul_eq_mul]

end Space
