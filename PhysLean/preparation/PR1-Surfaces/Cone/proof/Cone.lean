/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalCylinder
/-!

## One-nappe graph cone surface in `Space 3`

This file defines the one-nappe graph cone `z = a‖x‖` in `Space 3`, parametrized by
the transverse plane `Space 2`. The apex is included, but it is represented by the
single point `0 : Space 2`; the file does not assert smoothness there. When `a = 0`
the map degenerates to the coordinate plane. The associated measure is the pushforward
of planar volume weighted by the constant graph-area factor `√(a ^ 2 + 1)`.

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

## A. The definition of the one-nappe graph cone surface

-/

/-- The one-nappe graph cone `z = a‖x‖` in `Space 3`, parametrized by `Space 2`.

The apex is included as the image of `0`, but this definition does not assert smoothness
there. For `a = 0` this is the coordinate plane embedded in `Space 3`. -/
def cone (a : ℝ) : Space 2 → Space 3 := fun x =>
  (slice 2).symm (a * ‖x‖, x)

lemma cone_eq (a : ℝ) :
    cone a = (slice 2).symm ∘ (fun x : Space 2 => (a * ‖x‖, x)) := rfl

lemma cone_injective (a : ℝ) : Function.Injective (cone a) := by
  intro x y h
  have h' := congrArg (slice 2) h
  simp only [cone, ContinuousLinearEquiv.apply_symm_apply, Prod.mk.injEq] at h'
  exact h'.2

@[fun_prop]
lemma cone_continuous (a : ℝ) : Continuous (cone a) := by
  rw [cone_eq]
  fun_prop

lemma cone_measurableEmbedding (a : ℝ) : MeasurableEmbedding (cone a) :=
  Continuous.measurableEmbedding (cone_continuous a) (cone_injective a)

@[simp]
lemma norm_cone (a : ℝ) (x : Space 2) :
    ‖cone a x‖ = √(a ^ 2 + 1) * ‖x‖ := by
  rw [cone, norm_slice_symm_eq]
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have ha : 0 ≤ a ^ 2 + 1 := by nlinarith [sq_nonneg a]
  calc
    √(‖a * ‖x‖‖ ^ 2 + ‖x‖ ^ 2)
        = √((a ^ 2 + 1) * ‖x‖ ^ 2) := by
          congr 1
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
          nlinarith [sq_abs a]
    _ = √(a ^ 2 + 1) * √(‖x‖ ^ 2) := by
          rw [Real.sqrt_mul ha]
    _ = √(a ^ 2 + 1) * ‖x‖ := by
          rw [Real.sqrt_sq hx]

/-!

## B. The measure associated with the one-nappe graph cone

-/

/-- The measure on `Space 3` corresponding to integration over the one-nappe graph cone.

This is the pushforward of planar volume multiplied by the constant graph-area factor
`√(a ^ 2 + 1)`. It is not a formal result identifying the pushforward with Hausdorff
surface measure. -/
def coneMeasure (a : ℝ) : Measure (Space 3) :=
  MeasureTheory.Measure.map (cone a)
    (ENNReal.ofReal (√(a ^ 2 + 1)) • (volume : Measure (Space 2)))

instance coneMeasure_hasTemperateGrowth (a : ℝ) :
    (coneMeasure a).HasTemperateGrowth := by
  rw [coneMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨n, hn⟩ := MeasureTheory.Measure.HasTemperateGrowth.exists_integrable
    (μ := volume (α := Space 2))
  use n
  rw [MeasurableEmbedding.integrable_map_iff (cone_measurableEmbedding a)]
  change Integrable
    (fun x : Space 2 => (1 + ‖cone a x‖) ^ (-(n : ℝ)))
    (ENNReal.ofReal (√(a ^ 2 + 1)) • (volume : Measure (Space 2)))
  apply Integrable.smul_measure
  · apply Integrable.mono' hn
    · apply AEMeasurable.aestronglyMeasurable
      exact ((continuous_const.add (cone_continuous a).norm).rpow_const
        (fun x => Or.inl (by positivity : (1 : ℝ) + ‖cone a x‖ ≠ 0))).aemeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · have hle : ‖x‖ ≤ ‖cone a x‖ := by
          simp [cone]
        nlinarith
      · simp
  · exact ENNReal.ofReal_ne_top

instance coneMeasure_sFinite (a : ℝ) : SFinite (coneMeasure a) := by
  rw [coneMeasure]
  exact Measure.instSFiniteMap
    (ENNReal.ofReal (√(a ^ 2 + 1)) • (volume : Measure (Space 2))) (cone a)

/-!

## C. The distribution associated with the one-nappe graph cone

-/

/-- The distribution on `Space 3` corresponding to integration over the one-nappe graph cone. -/
def coneDist (a : ℝ) : (Space 3) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ (coneMeasure a)

lemma coneDist_apply_eq_integral_coneMeasure (a : ℝ) (f : 𝓢(Space 3, ℝ)) :
    coneDist a f = ∫ x, f x ∂coneMeasure a := by
  rw [coneDist, SchwartzMap.integralCLM_apply]

lemma coneDist_apply_eq_integral_volume (a : ℝ) (f : 𝓢(Space 3, ℝ)) :
    coneDist a f =
    ∫ x, f (cone a x)
      ∂(ENNReal.ofReal (√(a ^ 2 + 1)) • (volume : Measure (Space 2))) := by
  rw [coneDist_apply_eq_integral_coneMeasure, coneMeasure,
    MeasurableEmbedding.integral_map (cone_measurableEmbedding a)]

lemma coneDist_apply_eq_sqrt_mul_integral_volume (a : ℝ) (f : 𝓢(Space 3, ℝ)) :
    coneDist a f =
    √(a ^ 2 + 1) * ∫ x, f (cone a x) ∂(volume : Measure (Space 2)) := by
  rw [coneDist_apply_eq_integral_volume, integral_smul_measure, ENNReal.toReal_ofReal]
  · rfl
  · positivity

end Space
