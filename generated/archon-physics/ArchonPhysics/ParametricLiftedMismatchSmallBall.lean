import ArchonPhysics.ActualLiftedMismatchSmallBall

/-!
# Linear mismatch small balls with retained environment parameters

An augmented spectral chart retains the unselected masses as unchanged
environment coordinates.  This module supplies the measure-theoretic endpoint
for that construction: a bounded density in

`((child frequency pair, mismatch), environment)`

has a linear small-ball bound in the mismatch coordinate whenever the child
frequencies and the environment are restricted to finite-volume sets.

No spectral nondegeneracy is assumed here.  The intended upstream input is a
local quantitative Jacobian pushforward theorem for an augmented chart.
-/

namespace ArchonPhysics.ParametricLiftedMismatchSmallBall

open ArchonPhysics
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {E : Type*} [MeasurableSpace E]

local instance massTripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The mismatch coordinate of an augmented lifted point. -/
def parametricMismatch (point : MassTriple × E) : Real :=
  point.1.2

/-- Child-frequency cylinder with an additional environment restriction. -/
def parametricLiftedCylinder
    (ceiling : Real) (environment : Set E) : Set (MassTriple × E) :=
  liftedChildFrequencyCylinder ceiling ×ˢ environment

/-- A bounded mismatch slab with retained environment coordinates. -/
def parametricLiftedSlab
    (ceiling delta : Real) (environment : Set E) : Set (MassTriple × E) :=
  liftedMismatchSlab ceiling delta ×ˢ environment

theorem measurable_parametricMismatch :
    Measurable (parametricMismatch : MassTriple × E → Real) :=
  measurable_snd.comp measurable_fst

theorem measurableSet_parametricLiftedCylinder
    (ceiling : Real) {environment : Set E}
    (henvironment : MeasurableSet environment) :
    MeasurableSet (parametricLiftedCylinder ceiling environment) :=
  (measurableSet_liftedChildFrequencyCylinder ceiling).prod henvironment

theorem measurableSet_parametricLiftedSlab
    (ceiling delta : Real) {environment : Set E}
    (henvironment : MeasurableSet environment) :
    MeasurableSet (parametricLiftedSlab ceiling delta environment) :=
  (measurableSet_liftedMismatchSlab ceiling delta).prod henvironment

/-- Exact product-volume formula for the augmented bounded slab. -/
theorem volume_parametricLiftedSlab
    (ceiling : Real) (ν : Measure E) [SFinite ν] {delta : Real} (hdelta : 0 ≤ delta)
    {environment : Set E} (_henvironment : MeasurableSet environment) :
    ((volume : Measure MassTriple).prod ν)
        (parametricLiftedSlab ceiling delta environment) =
      ((ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          ENNReal.ofReal (2 * delta)) *
        ν environment := by
  change ((volume : Measure MassTriple).prod ν)
      (liftedMismatchSlab ceiling delta ×ˢ environment) = _
  rw [Measure.prod_prod, volume_liftedMismatchSlab ceiling hdelta]

/-- A full augmented density ceiling gives a linear mismatch small-ball bound
after retaining a finite-volume environment patch. -/
theorem map_parametricMismatch_absoluteMismatchSublevel_le
    (lifted : Measure (MassTriple × E)) (C : ENNReal) (ceiling : Real)
    (ν : Measure E) [SFinite ν]
    {environment : Set E} (henvironment : MeasurableSet environment)
    (hdensity : lifted ≤ C • ((volume : Measure MassTriple).prod ν))
    (hsupport : ∀ᵐ point ∂lifted,
      point ∈ parametricLiftedCylinder ceiling environment)
    {delta : Real} (hdelta : 0 ≤ delta) :
    Measure.map parametricMismatch lifted (absoluteMismatchSublevel delta) ≤
      C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
        ENNReal.ofReal (2 * delta) * ν environment := by
  have hwindow : MeasurableSet (absoluteMismatchSublevel delta) :=
    measurableSet_absoluteMismatchSublevel delta
  rw [Measure.map_apply measurable_parametricMismatch hwindow]
  have hrestrict :
      lifted.restrict (parametricLiftedCylinder ceiling environment) = lifted :=
    Measure.restrict_eq_self_of_ae_mem hsupport
  rw [← hrestrict,
    Measure.restrict_apply (hwindow.preimage measurable_parametricMismatch)]
  have hintersection :
      parametricMismatch ⁻¹' absoluteMismatchSublevel delta ∩
          parametricLiftedCylinder ceiling environment =
        parametricLiftedSlab ceiling delta environment := by
    ext point
    simp [parametricMismatch, parametricLiftedCylinder,
      parametricLiftedSlab, liftedChildFrequencyCylinder,
      liftedMismatchSlab, and_assoc, and_comm]
  rw [hintersection]
  calc
    lifted (parametricLiftedSlab ceiling delta environment) ≤
        (C • ((volume : Measure MassTriple).prod ν))
          (parametricLiftedSlab ceiling delta environment) :=
      hdensity (parametricLiftedSlab ceiling delta environment)
    _ = C * ((volume : Measure MassTriple).prod ν)
          (parametricLiftedSlab ceiling delta environment) := by
      simp only [Measure.smul_apply, smul_eq_mul]
    _ = C * (ENNReal.ofReal ceiling * ENNReal.ofReal ceiling) *
          ENNReal.ofReal (2 * delta) * ν environment := by
      rw [volume_parametricLiftedSlab ceiling ν hdelta henvironment]
      ring

end

end ArchonPhysics.ParametricLiftedMismatchSmallBall
