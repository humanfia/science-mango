import ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability
import ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit

/-!
# Closing canonical child-pair upper absolute continuity

This module specializes the unit-mass mismatch-kernel estimate to the actual
canonical marked law.  It proves that the lifted marked raw law is exactly the
corresponding pushforward of the deterministic Euclidean joint-frequency
limit.  A fixed Euclidean three-dimensional density upper bound therefore
gives a time-uniform planar upper bound for every broadened child law.

Finally, fixed measure domination is shown to be closed under weak convergence
of finite measures on the child plane.  Hence the same explicit raw-law bound
implies upper absolute continuity of the actual on-shell target, with no
assumption on the target trace itself.
-/

namespace ArchonPhysics.CanonicalOnShellChildPairUniformIntegrabilityClosure

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalOnShellChildPairTrace
open ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability
open ArchonPhysics.CanonicalOnShellChildPairUpperAbsoluteContinuity
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.ModalPhaseMismatch
open Filter
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The raw marked observable containing exactly the two child frequencies
and the scalar mismatch later tested by the resonance kernel. -/
def markedChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign)
    (marks : Fin 3 -> RankFrequencyMark) : (Real × Real) × Real :=
  childMismatchCoordinates markedChildFrequencyPair
    (markedFrequencyMismatch sign) marks

theorem continuous_markedChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign) :
    Continuous (markedChildMismatchCoordinates sign) := by
  unfold markedChildMismatchCoordinates childMismatchCoordinates
  exact continuous_markedChildFrequencyPair.prodMk
    (continuous_markedFrequencyMismatch sign)

theorem measurable_markedChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign) :
    Measurable (markedChildMismatchCoordinates sign) :=
  (continuous_markedChildMismatchCoordinates sign).measurable

/-- The same two child coordinates extracted from a Euclidean frequency
triple. -/
def euclideanChildFrequencyPair
    (frequency : EuclideanSpace Real (Fin 3)) : Real × Real :=
  ((euclideanFrequencyTripleToPlain frequency) 1,
    (euclideanFrequencyTripleToPlain frequency) 2)

theorem continuous_euclideanChildFrequencyPair :
    Continuous euclideanChildFrequencyPair := by
  unfold euclideanChildFrequencyPair
  exact ((continuous_apply 1).comp
    continuous_euclideanFrequencyTripleToPlain).prodMk
      ((continuous_apply 2).comp
        continuous_euclideanFrequencyTripleToPlain)

/-- Euclidean version of the lifted `(child pair, mismatch)` observable. -/
def euclideanChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign)
    (frequency : EuclideanSpace Real (Fin 3)) : (Real × Real) × Real :=
  childMismatchCoordinates euclideanChildFrequencyPair
    (euclideanFrequencyTripleMismatch sign) frequency

theorem continuous_euclideanChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign) :
    Continuous (euclideanChildMismatchCoordinates sign) := by
  unfold euclideanChildMismatchCoordinates childMismatchCoordinates
  exact continuous_euclideanChildFrequencyPair.prodMk
    (continuous_euclideanFrequencyTripleMismatch sign)

theorem measurable_euclideanChildMismatchCoordinates
    (sign : Fin 3 -> InteractionSign) :
    Measurable (euclideanChildMismatchCoordinates sign) :=
  (continuous_euclideanChildMismatchCoordinates sign).measurable

/-- Forgetting ranks before applying the Euclidean lifted observable is
exactly the direct marked lifted observable. -/
theorem euclideanChildMismatchCoordinates_comp_forgetRankFrequencyTripleEuclidean
    (sign : Fin 3 -> InteractionSign) :
    euclideanChildMismatchCoordinates sign ∘
        forgetRankFrequencyTripleEuclidean =
      markedChildMismatchCoordinates sign := by
  funext marks
  simp [euclideanChildMismatchCoordinates, childMismatchCoordinates,
    euclideanChildFrequencyPair, markedChildMismatchCoordinates,
    markedChildFrequencyPair, markedFrequencyMismatch,
    forgetRankFrequencyTripleEuclidean, forgetRankFrequencyTriple]

/-- The lifted raw marked law is not a new unknown measure: it is exactly the
lifted deterministic Euclidean joint-frequency per-site limit. -/
theorem map_markedChildMismatchCoordinates_raw_eq_euclidean
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    Measure.map (markedChildMismatchCoordinates sign)
        (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
          Measure (Fin 3 -> RankFrequencyMark)) =
      Measure.map (euclideanChildMismatchCoordinates sign)
        (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
          Measure (EuclideanSpace Real (Fin 3))) := by
  have hforget :
      Measure.map forgetRankFrequencyTripleEuclidean
          (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
            Measure (Fin 3 -> RankFrequencyMark)) =
        (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
          Measure (EuclideanSpace Real (Fin 3))) := by
    simpa only [FiniteMeasure.toMeasure_map] using
      congrArg FiniteMeasure.toMeasure
        (map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_forgetRankEuclidean
          ensemble)
  calc
    _ = Measure.map
        (euclideanChildMismatchCoordinates sign ∘
          forgetRankFrequencyTripleEuclidean)
        (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
          Measure (Fin 3 -> RankFrequencyMark)) := by
      rw [euclideanChildMismatchCoordinates_comp_forgetRankFrequencyTripleEuclidean]
    _ = Measure.map (euclideanChildMismatchCoordinates sign)
        (Measure.map forgetRankFrequencyTripleEuclidean
          (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
            Measure (Fin 3 -> RankFrequencyMark))) := by
      rw [Measure.map_map
        (measurable_euclideanChildMismatchCoordinates sign)
        measurable_forgetRankFrequencyTripleEuclidean]
    _ = _ := by rw [hforget]

/-- A three-dimensional density upper bound for the actual deterministic
Euclidean raw joint law yields the same time-independent planar bound for the
canonical broadened child law at every positive time. -/
theorem canonicalRankFrequencyMarkedBroadened_childPair_le_volume_of_euclidean_lifted_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hlifted :
      Measure.map (euclideanChildMismatchCoordinates sign)
          (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
            Measure (EuclideanSpace Real (Fin 3))) <=
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) :
    Measure.map markedChildFrequencyPair
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble sign T hT : Measure (Fin 3 -> RankFrequencyMark)) <=
      C • (volume : Measure (Real × Real)) := by
  apply map_broadenedResonanceMeasure_le_volume_of_lifted_le
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
    (measurable_markedFrequencyMismatch sign) hT
    markedChildFrequencyPair measurable_markedChildFrequencyPair C
  change Measure.map (markedChildMismatchCoordinates sign)
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble :
        Measure (Fin 3 -> RankFrequencyMark)) <=
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))
  exact (map_markedChildMismatchCoordinates_raw_eq_euclidean
    ensemble sign).trans_le hlifted

/-- Domination by one fixed outer-regular measure is closed under weak
convergence of finite measures on the child-frequency plane. -/
theorem childPlane_le_of_tendsto_of_forall_le
    (source : Nat -> FiniteMeasure (Real × Real))
    (target : FiniteMeasure (Real × Real))
    (reference : Measure (Real × Real))
    [reference.OuterRegular]
    (hweak : Tendsto source atTop (nhds target))
    (hle : forall n, (source n : Measure (Real × Real)) <= reference) :
    (target : Measure (Real × Real)) <= reference := by
  have hopen : forall U : Set (Real × Real), IsOpen U ->
      (target : Measure (Real × Real)) U <= reference U := by
    intro U hU
    by_cases hreference : reference U = ∞
    · simp [hreference]
    · rw [hU.measure_eq_biSup_integral_continuous
          (target : Measure (Real × Real))]
      simp only [iSup_le_iff]
      intro f hfContinuous hfSupport hfNonneg hfOne
      let test : BoundedContinuousFunction (Real × Real) Real :=
        BoundedContinuousFunction.ofNormedAddCommGroup f hfContinuous 1
          (fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg x)]
            exact hfOne x)
      have htendsto : Tendsto
          (fun n => ∫ x, f x ∂(source n : Measure (Real × Real)))
          atTop
          (nhds (∫ x, f x ∂(target : Measure (Real × Real))) ) := by
        simpa [test] using
          ((FiniteMeasure.tendsto_iff_forall_integral_tendsto).1 hweak test)
      have hreferenceIntegrable : Integrable f reference := by
        have hone : IntegrableOn (fun _x : Real × Real => (1 : Real))
            U reference := integrableOn_const hreference
        have hindicator := hone.integrable_indicator hU.measurableSet
        apply hindicator.mono'
          hfContinuous.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs]
        by_cases hx : x ∈ U
        · rw [abs_of_nonneg (hfNonneg x), indicator_of_mem hx]
          exact hfOne x
        · rw [indicator_of_notMem hx]
          have hzero := hfSupport hx
          simp [hzero]
      have hintegralLe :
          (∫ x, f x ∂(target : Measure (Real × Real))) <=
            ∫ x, f x ∂reference := by
        apply le_of_tendsto htendsto
        exact Eventually.of_forall fun n =>
          integral_mono_measure (hle n)
            (Eventually.of_forall hfNonneg) hreferenceIntegrable
      calc
        ENNReal.ofReal
            (∫ x, f x ∂(target : Measure (Real × Real))) <=
            ENNReal.ofReal (∫ x, f x ∂reference) :=
          ENNReal.ofReal_le_ofReal hintegralLe
        _ <= reference U :=
          integral_le_measure (fun x _hx => hfOne x)
            (fun x hx => le_of_eq (hfSupport hx))
  rw [Measure.le_iff']
  intro s
  rw [s.measure_eq_iInf_isOpen (target : Measure (Real × Real)),
    s.measure_eq_iInf_isOpen reference]
  exact iInf_mono fun U => iInf_mono fun _hsU =>
    iInf_mono fun hU => hopen U hU

/-- The raw Euclidean three-dimensional density upper bound closes the full
large-time upper-AC gap for every supplied actual canonical on-shell weak
limit.  No absolute-continuity premise on `target` is used. -/
theorem canonicalBroadenedWeakLimit_childPair_upperAbsoluteContinuity_of_euclidean_lifted_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (target : FiniteMeasure (Fin 3 -> RankFrequencyMark))
    (hweak : Tendsto
      (fun n =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n))
      atTop (nhds target))
    (C : ENNReal) (hC : C ≠ ∞)
    (hlifted :
      Measure.map
          (euclideanChildMismatchCoordinates
            RandomMassThreeWaveCollisionNetwork.decayInteractionSign)
          (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble :
            Measure (EuclideanSpace Real (Fin 3))) <=
        C • ((volume : Measure (Real × Real)).prod
          (volume : Measure Real))) :
    (Measure.map markedChildFrequencyPair target).restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) ≪
      volume.restrict
        (additiveFrequencyTriangle collisionFrequencyCeiling) := by
  have hprojected :=
    canonicalRankFrequencyMarkedBroadened_childPair_tendsto
      ensemble time htime_pos target hweak
  have hle : forall n,
      ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
          (time n) (htime_pos n)).map markedChildFrequencyPair :
        Measure (Real × Real)) <=
      C • (volume : Measure (Real × Real)) := by
    intro n
    exact
      canonicalRankFrequencyMarkedBroadened_childPair_le_volume_of_euclidean_lifted_le
        ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
        (htime_pos n) C hlifted
  let _ : (C • (volume : Measure (Real × Real))).OuterRegular :=
    Measure.OuterRegular.smul (volume : Measure (Real × Real)) hC
  have htargetLe : Measure.map markedChildFrequencyPair target <=
      C • (volume : Measure (Real × Real)) := by
    exact childPlane_le_of_tendsto_of_forall_le
      (fun n =>
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
            (time n) (htime_pos n)).map markedChildFrequencyPair)
      (target.map markedChildFrequencyPair)
      (C • (volume : Measure (Real × Real))) hprojected hle
  exact (Measure.absolutelyContinuous_of_le_smul htargetLe).restrict
    (additiveFrequencyTriangle collisionFrequencyCeiling)

end

end ArchonPhysics.CanonicalOnShellChildPairUniformIntegrabilityClosure
