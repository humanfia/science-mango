import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualOppositeEndpointRootEncCardV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic finite general-position data for actual tubes

Every finite tube family admits a canonical real-valued injective weight:
enumerate its membership subtype and cast the resulting finite index to
`Real`.  For a common-`c` family, critical height differences are finite
without a further general-position hypothesis.  Indeed, the equality of
first derivatives is the zero set of the reduced first trace jet.  If both
reduced derivative coefficients vanish, the height difference is constant.
Otherwise the linear-dominant branch has no zero, while the quadratic-
dominant branch has at most one zero by the existing strict-monotonicity
root lemma.
-/

/-- Canonical global real weight attached to a finite set.  Values away from
the finset are irrelevant to the perturbation and are set to zero. -/
def finiteFinsetRealWeight {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (x : alpha) : Real :=
  if hx : x ∈ s then
    ((Fintype.equivFin {y : alpha // y ∈ s}) ⟨x, hx⟩ : Nat)
  else 0

/-- The canonical weight is injective on the finset for which it was
constructed. -/
theorem finiteFinsetRealWeight_injOn
    {alpha : Type*} [DecidableEq alpha] (s : Finset alpha) :
    Set.InjOn (finiteFinsetRealWeight s) (s : Set alpha) := by
  intro x hx y hy hxy
  change x ∈ s at hx
  change y ∈ s at hy
  simp only [finiteFinsetRealWeight, dif_pos hx, dif_pos hy] at hxy
  have hfin :
      Fintype.equivFin {z : alpha // z ∈ s} ⟨x, hx⟩ =
        Fintype.equivFin {z : alpha // z ∈ s} ⟨y, hy⟩ := by
    apply Fin.ext
    exact_mod_cast hxy
  exact congrArg Subtype.val
    ((Fintype.equivFin {z : alpha // z ∈ s}).injective hfin)

/-- Tube-specialized name used by the endpoint connector. -/
def finiteActualTubeWeight {radius : NNReal}
    (curves : Finset (Tube radius)) : Tube radius -> Real :=
  finiteFinsetRealWeight curves

theorem finiteActualTubeWeight_injOn {radius : NNReal}
    (curves : Finset (Tube radius)) :
    Set.InjOn (finiteActualTubeWeight curves)
      (curves : Set (Tube radius)) := by
  exact finiteFinsetRealWeight_injOn curves

/-- On a common `c` slice, the difference of actual first derivatives is the
literal reduced first trace derivative. -/
theorem actualTubeGraphFirst_sub_eq_traceFirstDerivative
    {radius : NNReal} (T U : Tube radius) (f f1 : Real -> Real)
    (hcommonC : tubeGraphC T = tubeGraphC U) (theta : Real) :
    actualTubeGraphFirst T f f1 theta -
        actualTubeGraphFirst U f f1 theta =
      traceFirstDerivative f f1
        (tubePairDeltaB T U) (tubePairDeltaD T U) theta := by
  simp only [actualTubeGraphFirst, cinematicTraceFirstValue,
    traceFirstDerivative, traceJet1, tubePairDeltaB, tubePairDeltaD,
    skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD,
    tubeGraphB, tubeGraphC, tubeGraphD] at hcommonC ⊢
  rw [hcommonC]
  ring

/-- The critical-height set of two actual tubes in a common `c` slice is
finite under the paper's quantitative `f,f',f''` regime.  No arbitrary
critical-set callback and no coefficient-positivity hypothesis is needed. -/
theorem actualTube_criticalHeightDifferenceSet_finite
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) {A B : Real}
    (hAB : A <= B)
    (hcommonC : tubeGraphC T = tubeGraphC U)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B)) :
    (criticalHeightDifferenceSet
      (fun X => actualTubeGraph X f)
      (fun X => actualTubeGraphFirst X f f1) A B T U).Finite := by
  let db : Real := tubePairDeltaB T U
  let dd : Real := tubePairDeltaD T U
  by_cases hzero : db = 0 ∧ dd = 0
  · rcases hzero with ⟨hdb, hdd⟩
    apply (Set.finite_singleton
      (tubeGraphA U - tubeGraphA T)).subset
    rintro v ⟨theta, _htheta, _hfirst, hv⟩
    have hb : tubeGraphB T = tubeGraphB U := by
      exact sub_eq_zero.mp (by simpa only [db, tubePairDeltaB] using hdb)
    have hd : tubeGraphD T = tubeGraphD U := by
      exact sub_eq_zero.mp (by simpa only [dd, tubePairDeltaD] using hdd)
    have hb' : skirtTubeGraphB T = skirtTubeGraphB U := by
      simpa only [skirtTubeGraphB, skirtTubeGraphD, tubeGraphB,
        tubeGraphD] using hb
    have hc' : skirtTubeGraphC T = skirtTubeGraphC U := by
      simpa only [skirtTubeGraphC, tubeGraphC] using hcommonC
    have hd' : skirtTubeGraphD T = skirtTubeGraphD U := by
      simpa only [skirtTubeGraphD, tubeGraphD] using hd
    have hv' : v = tubeGraphA U - tubeGraphA T := by
      change v = skirtTubeGraphA U - skirtTubeGraphA T
      rw [hv]
      simp only [actualTubeGraph]
      rw [hb', hc', hd']
      ring
    exact Set.mem_singleton_iff.mpr hv'
  · have hcriticalSubset :
        criticalHeightDifferenceSet
            (fun X => actualTubeGraph X f)
            (fun X => actualTubeGraphFirst X f f1) A B T U ⊆
          (fun theta => actualTubeGraph U f theta -
              actualTubeGraph T f theta) ''
            {theta | theta ∈ Icc A B ∧
              traceFirstDerivative f f1 db dd theta = 0} := by
      rintro v ⟨theta, htheta, hfirst, rfl⟩
      refine ⟨theta, ⟨htheta, ?_⟩, rfl⟩
      have hdiff := actualTubeGraphFirst_sub_eq_traceFirstDerivative
        T U f f1 hcommonC theta
      change actualTubeGraphFirst T f f1 theta =
        actualTubeGraphFirst U f f1 theta at hfirst
      rw [hfirst, sub_self] at hdiff
      simpa only [db, dd] using hdiff.symm
    apply (Set.Finite.image
      (fun theta => actualTubeGraph U f theta -
        actualTubeGraph T f theta) ?_).subset hcriticalSubset
    by_cases hlinear : 10 * |dd| <= |db|
    · apply Set.finite_empty.subset
      intro theta htheta
      have hdbNe : db ≠ 0 := by
        intro hdb
        have hdd : dd = 0 := by
          rw [hdb, abs_zero] at hlinear
          have : |dd| = 0 := by
            nlinarith [abs_nonneg dd]
          exact abs_eq_zero.mp this
        exact hzero ⟨hdb, hdd⟩
      have hlarge := traceJet1_large_of_linear_dominates
        db dd (f theta) (f1 theta) theta
        (hparameter theta htheta.1) (hft theta htheta.1)
        (hf1Lower theta htheta.1) (hf1Upper theta htheta.1) hlinear
      have hlarge' : |db| / 2 <=
          |traceFirstDerivative f f1 db dd theta| := by
        simpa only [traceFirstDerivative] using hlarge
      rw [htheta.2, abs_zero] at hlarge'
      have : 0 < |db| := abs_pos.mpr hdbNe
      exfalso
      nlinarith
    · have hquadratic : |db| < 10 * |dd| := lt_of_not_ge hlinear
      have hddNe : dd ≠ 0 := by
        intro hdd
        rw [hdd, abs_zero, mul_zero] at hquadratic
        exact (not_lt_of_ge (abs_nonneg db)) hquadratic
      have hkappa : 0 < |dd| := abs_pos.mpr hddNe
      have hfirstDeriv : forall z, z ∈ Icc A B ->
          HasDerivAt (traceFirstDerivative f f1 db dd)
            (traceSecondDerivative f1 f2 db dd z) z := by
        intro z hz
        exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
          (hfDeriv z hz) (hf1Deriv z hz)
      have hf1Continuous : ContinuousOn f1 (Icc A B) :=
        HasDerivAt.continuousOn hf1Deriv
      have hsecondContinuous :
          ContinuousOn (traceSecondDerivative f1 f2 db dd)
            (Icc A B) := by
        unfold traceSecondDerivative traceJet2
        fun_prop
      apply Set.finite_of_encard_le_coe
      apply absFirstDerivative_rootSet_encard_le_one
        (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd)
        hAB hkappa hfirstDeriv hsecondContinuous
      intro z hz
      simpa only [traceSecondDerivative] using
        (traceJet2_large_of_quadratic_dominates
          db dd (f1 z) (f2 z) z
          (hparameter z hz) (hf1Lower z hz) (hf2 z hz) hquadratic)

/-- Family form consumed by the finite general-position producer. -/
theorem actualTube_family_criticalHeightDifferenceSet_finite
    {radius : NNReal} (curves : Finset (Tube radius))
    (f f1 f2 : Real -> Real) {A B : Real}
    (hAB : A <= B)
    (hcommonC : forall V, V ∈ curves -> forall W, W ∈ curves ->
      tubeGraphC V = tubeGraphC W)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B)) :
    forall V, V ∈ curves -> forall W, W ∈ curves -> V ≠ W ->
      (criticalHeightDifferenceSet
        (fun X => actualTubeGraph X f)
        (fun X => actualTubeGraphFirst X f f1) A B V W).Finite := by
  intro V hV W hW _hVW
  exact actualTube_criticalHeightDifferenceSet_finite V W f f1 f2 hAB
    (hcommonC V hV W hW) hparameter hft hf1Lower hf1Upper hf2
    hfDeriv hf1Deriv hf2Continuous


/-- Direct endpoint consumer: choose the canonical finite-family weight and
discharge every critical-height finiteness premise from the actual cinematic
regime.  Compared with the underlying endpoint theorem, neither `weight`,
`InjOn weight`, nor a pairwise `criticalHeightDifferenceSet.Finite` callback
is exposed. -/
theorem exists_perturbedRetainedPairEndpointAssembly_of_automaticGeneralPosition
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (hfiber : fiber.Nonempty)
    (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    (center : C2GraphRectangle) {domain : Set Real}
    {A B delta t lambda0 lambda1 comparisonLambda
      externalTolerance : Real}
    (hexternalTolerance : 0 < externalTolerance)
    (hAB : A < B) (hdelta : 0 < delta) (ht : 0 < t)
    (hlambda1 : 1 <= lambda1)
    (hwidth : (1 / 2 : Real) <= B - A)
    (P : forall i, i ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T i) (U i) f (sourceRectangles i)
          A B delta t lambda0 lambda1)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda1) * delta <
      t / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcommonC : forall V, V ∈ retainedPairTubeFamily fiber T U -> forall W,
      W ∈ retainedPairTubeFamily fiber T U -> tubeGraphC V = tubeGraphC W)
    (henlarge : 2 * lambda1 * delta <= comparisonLambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda1) delta t <=
      Real.sqrt (comparisonLambda * delta / t))
    (hreference : forall epsilon, 0 < epsilon ->
      epsilon < externalTolerance -> forall V,
      V ∈ perturbedRetainedTubeFamily fiber T U
        (finiteActualTubeWeight (retainedPairTubeFamily fiber T U)) epsilon ->
        InPointwiseC2BallOn domain center
          (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv
            A B hAB.le) (3 * t))
    (hpairwise : Set.Pairwise (fiber : Set alpha)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (sourceRectangles i) (sourceRectangles j)
          delta t comparisonLambda))) :
    Nonempty (PerturbedRetainedPairEndpointAssembly fiber T U
      sourceRectangles
      (finiteActualTubeWeight (retainedPairTubeFamily fiber T U))
      f f1 center domain A B delta t lambda1 comparisonLambda
        externalTolerance) := by
  apply exists_perturbedRetainedPairEndpointAssembly_of_perturbationReady
    fiber hfiber T U sourceRectangles
    (finiteActualTubeWeight (retainedPairTubeFamily fiber T U))
    f f1 f2 center hexternalTolerance hAB hdelta ht hlambda1 hwidth P
    hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower hf1Upper hf2
    hf2Continuous hcommonC
    (finiteActualTubeWeight_injOn (retainedPairTubeFamily fiber T U))
  · exact actualTube_family_criticalHeightDifferenceSet_finite
      (retainedPairTubeFamily fiber T U) f f1 f2 hAB.le hcommonC
      hparameter hft hf1Lower hf1Upper hf2
      (fun z _hz => hfDeriv z) (fun z _hz => hf1Deriv z) hf2Continuous
  · exact henlarge
  · exact hscale
  · exact hreference
  · exact hpairwise
#print axioms finiteFinsetRealWeight_injOn
#print axioms finiteActualTubeWeight_injOn
#print axioms actualTubeGraphFirst_sub_eq_traceFirstDerivative
#print axioms actualTube_criticalHeightDifferenceSet_finite
#print axioms actualTube_family_criticalHeightDifferenceSet_finite
#print axioms exists_perturbedRetainedPairEndpointAssembly_of_automaticGeneralPosition

end

end FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
