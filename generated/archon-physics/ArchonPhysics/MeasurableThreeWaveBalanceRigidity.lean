import ArchonPhysics.MeasurableIntervalAdditiveRigidity
import ArchonPhysics.ContinuousThreeWaveBalanceAEBounded
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Measurable three-wave balance rigidity

A collision-a.e. balance law for a measurable, interval-integrable frequency
profile is transferred to planar Lebesgue measure by the lower child-pair
trace domination.  The interval a.e. Cauchy theorem then classifies the
profile, and the opposite trace domination transfers that classification back
to all three collision legs.  Thus the trace condition is equivalence of null
sets on the additive triangle; no continuous representative is assumed.

The final theorem accepts `MemLp profile ∞` on the compact frequency interval,
which is the interface needed by canonical L-infinity inverse actions.
-/

namespace ArchonPhysics.MeasurableThreeWaveBalanceRigidity

open Set MeasureTheory
open ArchonPhysics
open ArchonPhysics.AdditiveTriangleMeasureSupport
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.MeasurableIntervalAdditiveRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

theorem childPair_ae_mem_triangle
    (collision : ResonantThreeWaveMeasure Mode) {W : Real}
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W) :
    ∀ᵐ pair ∂childFrequencyPairMeasure collision,
      pair ∈ additiveFrequencyTriangle W := by
  have htriad :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        childFrequencyPair collision triad ∈ additiveFrequencyTriangle W := by
    filter_upwards [collision.resonance_ae, hfrequency] with triad hres hfreq
    exact ⟨(hfreq 1).1, (hfreq 2).1, hres ▸ (hfreq 0).2⟩
  unfold childFrequencyPairMeasure
  exact (ae_map_iff (measurable_childFrequencyPair collision).aemeasurable
    (isClosed_additiveFrequencyTriangle W).measurableSet).2 htriad

theorem measurable_profile_balance_volume_ae
    (collision : ResonantThreeWaveMeasure Mode) {W : Real}
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    {profile : Real -> Real} (hprofile : Measurable profile)
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (htrace : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W)) :
    ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2 := by
  let balanceSet : Set (Real × Real) :=
    {pair | pair ∈ additiveFrequencyTriangle W ∧
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2}
  have hbalanceSet : MeasurableSet balanceSet := by
    dsimp [balanceSet]
    exact (isClosed_additiveFrequencyTriangle W).measurableSet.inter
      (measurableSet_eq_fun
        (hprofile.comp (measurable_fst.add measurable_snd))
        ((hprofile.comp measurable_fst).add (hprofile.comp measurable_snd)))
  have htriad :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        childFrequencyPair collision triad ∈ balanceSet := by
    filter_upwards [collision.resonance_ae, hfrequency, hbalance] with
      triad hres hfreq hbal
    constructor
    · exact ⟨(hfreq 1).1, (hfreq 2).1, hres ▸ (hfreq 0).2⟩
    · simpa only [childFrequencyPair, hres] using hbal
  have hpair :
      ∀ᵐ pair ∂childFrequencyPairMeasure collision, pair ∈ balanceSet := by
    unfold childFrequencyPairMeasure
    exact (ae_map_iff (measurable_childFrequencyPair collision).aemeasurable
      hbalanceSet).2 htriad
  have hrestricted :
      ∀ᵐ pair ∂(childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W),
        profile (pair.1 + pair.2) = profile pair.1 + profile pair.2 := by
    apply ae_restrict_of_ae
    filter_upwards [hpair] with pair hp
    exact hp.2
  exact htrace.ae_le hrestricted

theorem measurableFrequencyProfile_linear_volume_ae_of_equivalentTrace
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    {profile : Real -> Real} (hprofile : Measurable profile)
    (hintegrable : IntegrableOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (htrace : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W)) :
    ∃ beta : Real,
      ∀ᵐ omega ∂volume.restrict (Icc (0 : Real) W),
        profile omega = beta * omega := by
  exact integrable_interval_ae_additive_linear hW hintegrable
    (measurable_profile_balance_volume_ae collision hfrequency hprofile
      hbalance htrace)

theorem interval_ae_lifts_to_triangle_ae
    {W : Real} {p : Real -> Prop}
    (hp : ∀ᵐ omega ∂volume.restrict (Icc (0 : Real) W), p omega) :
    ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
      p pair.1 ∧ p pair.2 ∧ p (pair.1 + pair.2) := by
  have hpGlobal : ∀ᵐ omega ∂(volume : Measure Real),
      omega ∈ Icc (0 : Real) W -> p omega :=
    (ae_restrict_iff' measurableSet_Icc).1 hp
  have hfirst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure Real)) (ν := (volume : Measure Real))).ae hpGlobal
  have hsecond := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure Real)) (ν := (volume : Measure Real))).ae hpGlobal
  have hsumQMP : Measure.QuasiMeasurePreserving
      (fun pair : Real × Real => pair.1 + pair.2)
      ((volume : Measure Real).prod volume) volume := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure Real)) (ν := (volume : Measure Real))).comp
        (measurePreserving_add_prod
          (volume : Measure Real) (volume : Measure Real)).quasiMeasurePreserving
  have hsum := hsumQMP.ae hpGlobal
  have hall : ∀ᵐ pair ∂((volume : Measure Real).prod volume),
      pair ∈ additiveFrequencyTriangle W ->
        p pair.1 ∧ p pair.2 ∧ p (pair.1 + pair.2) := by
    filter_upwards [hfirst, hsecond, hsum] with pair h1 h2 hs
    intro hpair
    exact ⟨h1 ⟨hpair.1,
        (le_add_of_nonneg_right hpair.2.1).trans hpair.2.2⟩,
      h2 ⟨hpair.2.1,
        (le_add_of_nonneg_left hpair.1).trans hpair.2.2⟩,
      hs ⟨add_nonneg hpair.1 hpair.2.1, hpair.2.2⟩⟩
  rw [← Measure.volume_eq_prod] at hall
  exact (ae_restrict_iff'
    (isClosed_additiveFrequencyTriangle W).measurableSet).2 hall

theorem measurableFrequencyProfile_ae_proportional_of_equivalentTrace
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    {profile : Real -> Real} (hprofile : Measurable profile)
    (hintegrable : IntegrableOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hlower : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W))
    (hupper : (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W) ≪
      volume.restrict (additiveFrequencyTriangle W)) :
    ∃ beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  obtain ⟨beta, hlinear⟩ :=
    measurableFrequencyProfile_linear_volume_ae_of_equivalentTrace
      collision hW hfrequency hprofile hintegrable hbalance hlower
  refine ⟨beta, ?_⟩
  let p : Real -> Prop := fun omega => profile omega = beta * omega
  have hpairVolume := interval_ae_lifts_to_triangle_ae (p := p) hlinear
  have hpairRestricted :
      ∀ᵐ pair ∂(childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W),
        p pair.1 ∧ p pair.2 ∧ p (pair.1 + pair.2) :=
    hupper.ae_le hpairVolume
  have hpairMem := childPair_ae_mem_triangle collision hfrequency
  have hrestrict :
      (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W) =
        childFrequencyPairMeasure collision :=
    Measure.restrict_eq_self_of_ae_mem hpairMem
  rw [hrestrict] at hpairRestricted
  have hpairPredicate : MeasurableSet
      {pair : Real × Real | p pair.1 ∧ p pair.2 ∧ p (pair.1 + pair.2)} := by
    dsimp [p]
    exact (measurableSet_eq_fun (hprofile.comp measurable_fst)
      (measurable_const.mul measurable_fst)).inter
      ((measurableSet_eq_fun (hprofile.comp measurable_snd)
        (measurable_const.mul measurable_snd)).inter
      (measurableSet_eq_fun
        (hprofile.comp (measurable_fst.add measurable_snd))
        (measurable_const.mul (measurable_fst.add measurable_snd))))
  have htriad :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        p (collision.frequency (triad 0)) ∧
          p (collision.frequency (triad 1)) ∧
            p (collision.frequency (triad 2)) := by
    have hpull :
        ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
          p (collision.frequency (triad 1)) ∧
            p (collision.frequency (triad 2)) ∧
              p (collision.frequency (triad 1) +
                collision.frequency (triad 2)) := by
      unfold childFrequencyPairMeasure at hpairRestricted
      exact (ae_map_iff (measurable_childFrequencyPair collision).aemeasurable
        hpairPredicate).1 hpairRestricted
    filter_upwards [hpull, collision.resonance_ae] with triad hp hres
    exact ⟨hres ▸ hp.2.2, hp.1, hp.2.1⟩
  have hleg (leg : Fin 3) :
      ∀ᵐ mode ∂legMarginal collision leg,
        p (collision.frequency mode) := by
    unfold legMarginal
    have hset : MeasurableSet {mode | p (collision.frequency mode)} := by
      dsimp [p]
      exact measurableSet_eq_fun
        (hprofile.comp collision.measurable_frequency)
        (measurable_const.mul collision.measurable_frequency)
    exact (ae_map_iff (measurable_triadLeg leg).aemeasurable hset).2 (by
      filter_upwards [htriad] with triad ht
      fin_cases leg
      · exact ht.1
      · exact ht.2.1
      · exact ht.2.2)
  rw [collisionReferenceMeasure, ae_add_measure_iff, ae_add_measure_iff]
  exact ⟨⟨hleg 0, hleg 1⟩, hleg 2⟩

/-- An essentially bounded measurable profile is integrable on the finite
frequency interval, so the measurable rigidity theorem applies directly to
an `Lp Real ∞` representative. -/
theorem measurableFrequencyProfile_ae_proportional_of_memLp_top_equivalentTrace
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        forall leg : Fin 3,
          collision.frequency (triad leg) ∈ Icc (0 : Real) W)
    {profile : Real -> Real} (hprofile : Measurable profile)
    (hmemLp : MemLp profile ∞ (volume.restrict (Icc (0 : Real) W)))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hlower : volume.restrict (additiveFrequencyTriangle W) ≪
      (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W))
    (hupper : (childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W) ≪
      volume.restrict (additiveFrequencyTriangle W)) :
    ∃ beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  apply measurableFrequencyProfile_ae_proportional_of_equivalentTrace
    collision hW hfrequency hprofile
  · exact hmemLp.integrable (by simp)
  · exact hbalance
  · exact hlower
  · exact hupper

end

end ArchonPhysics.MeasurableThreeWaveBalanceRigidity
