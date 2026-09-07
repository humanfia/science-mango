import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizedDatumV1
import FamilyStickyCinematicL32WZL3UniformTubeSourceV1

/-!
# Eighth-normalized WZL3 sources

The B2 normalization leaves every tube direction unchanged.  Hence a
vertical WZL3 source remains a vertical WZL3 source at radius `radius / 8`.
This small adapter exposes that literal source together with the exact
average and unit-ball transports used by the full-coefficient proxy.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EighthNormalizedWZL3SourceV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section


/-- Eighth normalization preserves the literal WZL3 source indices and
their vertical direction certificate. -/
def eighthNormalizedWZL3Source
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota) :
    WZL3UniformTubeSource (radius / 8) iota where
  family := eighthNormalizedTubeFamily S.family
  source := S.source
  source_direction_final_half i hi := by
    simpa only [eighthNormalizedTubeFamily_tubes,
      eighthNormalizedTube_axis, eighthNormalizedAxis_direction] using
        S.source_direction_final_half i hi

@[simp] theorem eighthNormalizedWZL3Source_family
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota) :
    (eighthNormalizedWZL3Source S).family =
      eighthNormalizedTubeFamily S.family :=
  rfl

@[simp] theorem eighthNormalizedWZL3Source_source
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota) :
    (eighthNormalizedWZL3Source S).source = S.source :=
  rfl

/-- The normalized chart shading has exactly the original average
multiplicity. -/
theorem eighthNormalizedWZL3Shading_averageMultiplicity
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) :
    (eighthNormalizedShading S.family Y).averageMultiplicity =
      Y.averageMultiplicity :=
  eighthNormalizedShading_averageMultiplicity S.family Y

/-- Literal B2 support on selected source indices becomes unit-ball support
after eighth normalization. -/
theorem eighthNormalizedWZL3Source_active_carrier_subset_unitBall
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (active : Finset iota)
    (hB2 : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2) :
    ∀ i, i ∈ active →
      ((eighthNormalizedWZL3Source S).family.tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
  intro i hi
  change (eighthNormalizedTube (S.family.tubes i)).carrier ⊆
    Metric.closedBall (0 : Space) 1
  exact eighthNormalizedTube_carrier_subset_unitBall
    (S.family.tubes i) hradiusHalf (hB2 i hi)

#print axioms eighthNormalizedWZL3Source
#print axioms eighthNormalizedWZL3Shading_averageMultiplicity
#print axioms
  eighthNormalizedWZL3Source_active_carrier_subset_unitBall

end
end Family8EighthNormalizedWZL3SourceV3
