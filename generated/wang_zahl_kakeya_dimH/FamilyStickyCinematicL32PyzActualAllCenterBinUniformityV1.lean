import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
import FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
import FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1

noncomputable section

/-!
# Exact uniformity of the two post-norm dyadic losses

After the norm scale is fixed, the tangency ceiling is the same
`36 * globalScale` for every cover centre.  Moreover the stored `Y₁`
shading deliberately retains the original finite ambient index set, so its
final positive-multiplicity bin count is definitionally independent of the
centre and equals the bin count formed from `ambient.card`.
-/

universe u v

/-- The centered-half localized tangency stage does not replace the ambient
index set. -/
theorem actualProjectedCenteredHalfTangencyY1_ambient_eq
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) :
    (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold).ambient = physical.ambient := by
  rfl

/-- Consequently the final dyadic multiplicity-bin loss is exactly the same
for all norm-cover centres. -/
theorem actualProjectedCenteredHalfTangencyY1_finalBinFactor_eq
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold : Real) :
    continuumCriticalSingleDyadicBinFactor 1
        (((actualProjectedCenteredHalfTangencyY1 base hbase fine physical
          f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
          ceiling exponent threshold).ambient.card : Nat) : Real) =
      continuumCriticalSingleDyadicBinFactor 1
        ((physical.ambient.card : Nat) : Real) := by
  rw [actualProjectedCenteredHalfTangencyY1_ambient_eq]

/-- The common two-stage post-norm selection loss. -/
def actualAllCenterPostNormBinLoss
    (radius : NNReal) (globalScale : Real) (ambientCard : Nat) : ENNReal :=
  (continuumCriticalSingleDyadicBinFactor (radius : Real)
      (36 * globalScale) : ENNReal) *
    (continuumCriticalSingleDyadicBinFactor 1
      (ambientCard : Real) : ENNReal)

/-- Literal per-centre tangency/E₂ losses reduce to one common loss. -/
theorem actualProjectedCenteredHalfTangencyY1_twoBinLoss_eq_common
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (exponent threshold : Real) :
    (continuumCriticalSingleDyadicBinFactor (radius : Real)
        (36 * globalScale) : ENNReal) *
      (continuumCriticalSingleDyadicBinFactor 1
        (((actualProjectedCenteredHalfTangencyY1 base hbase fine physical
          f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
          (36 * globalScale) exponent threshold).ambient.card : Nat) : Real) :
          ENNReal) =
      actualAllCenterPostNormBinLoss radius globalScale
        physical.ambient.card := by
  rw [actualProjectedCenteredHalfTangencyY1_finalBinFactor_eq]
  rfl

#print axioms actualProjectedCenteredHalfTangencyY1_ambient_eq
#print axioms actualProjectedCenteredHalfTangencyY1_finalBinFactor_eq
#print axioms actualAllCenterPostNormBinLoss
#print axioms actualProjectedCenteredHalfTangencyY1_twoBinLoss_eq_common

end

end FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
