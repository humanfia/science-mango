import ArchonPhysics.ContinuousIntervalAdditiveRigidity
import ArchonPhysics.ResonantThreeWaveKineticEquilibrium
import Mathlib.MeasureTheory.Measure.Support

/-!
# Continuous three-wave frequency-balance rigidity

This module connects compact-interval Cauchy rigidity to the collision-measure
interfaces used by the continuum three-wave kinetic equilibrium module.

For a resonant collision measure, its child-frequency-pair measure is the
pushforward to `(omega_1, omega_2)`.  If the restriction of this pair measure
to the closed additive triangle has the whole triangle in its topological
support, then an almost-everywhere balance identity for a continuous
frequency-only profile upgrades to a pointwise identity on the triangle.
Restricted continuous Cauchy rigidity then makes the profile linear.

The full-support hypothesis is explicit.  In particular, this module does not
claim that a canonical thermodynamic collision measure has that support, and
it does not claim that every abstract balanced mode weight factors continuously
through frequency.
-/

namespace ArchonPhysics.ContinuousThreeWaveBalanceRigidity

open Set MeasureTheory
open ArchonPhysics.ContinuousIntervalAdditiveRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

noncomputable section

/-- The closed child-frequency simplex compatible with a decay resonance and
an upper frequency bound `W`. -/
def additiveFrequencyTriangle (W : Real) : Set (Real × Real) :=
  {pair | 0 <= pair.1 ∧ 0 <= pair.2 ∧ pair.1 + pair.2 <= W}

/-- The additive frequency triangle is closed. -/
theorem isClosed_additiveFrequencyTriangle (W : Real) :
    IsClosed (additiveFrequencyTriangle W) := by
  have hfst : Continuous (fun pair : Real × Real => pair.1) := continuous_fst
  have hsnd : Continuous (fun pair : Real × Real => pair.2) := continuous_snd
  have hzero : Continuous (fun _ : Real × Real => (0 : Real)) :=
    continuous_const
  have hW : Continuous (fun _ : Real × Real => W) := continuous_const
  rw [show additiveFrequencyTriangle W = {p : Real × Real | 0 <= p.1} ∩
      ({p : Real × Real | 0 <= p.2} ∩
        {p : Real × Real | p.1 + p.2 <= W}) by
    ext p
    simp only [additiveFrequencyTriangle, mem_ofPred_eq, mem_inter_iff]]
  exact (isClosed_le hzero hfst).inter
    ((isClosed_le hzero hsnd).inter (isClosed_le (hfst.add hsnd) hW))

/-- For a profile continuous on `[0, W]`, its balance locus inside the
additive frequency triangle is closed in the ambient pair space. -/
theorem isClosed_frequencyBalanceSet
    {profile : Real -> Real} {W : Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W)) :
    IsClosed {pair ∈ additiveFrequencyTriangle W |
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2} := by
  have hsum_mem : forall pair, pair ∈ additiveFrequencyTriangle W ->
      pair.1 + pair.2 ∈ Icc (0 : Real) W := by
    intro pair hpair
    exact ⟨add_nonneg hpair.1 hpair.2.1, hpair.2.2⟩
  have hfst_mem : forall pair, pair ∈ additiveFrequencyTriangle W ->
      pair.1 ∈ Icc (0 : Real) W := by
    intro pair hpair
    exact ⟨hpair.1,
      (le_add_of_nonneg_right hpair.2.1).trans hpair.2.2⟩
  have hsnd_mem : forall pair, pair ∈ additiveFrequencyTriangle W ->
      pair.2 ∈ Icc (0 : Real) W := by
    intro pair hpair
    exact ⟨hpair.2.1,
      (le_add_of_nonneg_left hpair.1).trans hpair.2.2⟩
  have hleft : ContinuousOn (fun pair : Real × Real =>
      profile (pair.1 + pair.2)) (additiveFrequencyTriangle W) :=
    hprofile.comp (continuous_fst.add continuous_snd).continuousOn hsum_mem
  have hright : ContinuousOn (fun pair : Real × Real =>
      profile pair.1 + profile pair.2) (additiveFrequencyTriangle W) :=
    (hprofile.comp continuous_fst.continuousOn hfst_mem).add
      (hprofile.comp continuous_snd.continuousOn hsnd_mem)
  exact (isClosed_additiveFrequencyTriangle W).isClosed_eq hleft hright

/-- An almost-everywhere balance identity becomes pointwise throughout the
closed triangle when the restricted pair measure has full relative support
there. -/
theorem continuousOn_frequencyBalance_of_ae_restrict_of_fullSupport
    {profile : Real -> Real} {W : Real}
    {pairMeasure : Measure (Real × Real)}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hfullSupport : additiveFrequencyTriangle W ⊆
      (pairMeasure.restrict (additiveFrequencyTriangle W)).support)
    (hbalance : ∀ᵐ pair ∂pairMeasure.restrict (additiveFrequencyTriangle W),
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2) :
    forall pair, pair ∈ additiveFrequencyTriangle W ->
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2 := by
  have hclosed := isClosed_frequencyBalanceSet hprofile
  have hconull : {pair ∈ additiveFrequencyTriangle W |
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2} ∈
        ae (pairMeasure.restrict (additiveFrequencyTriangle W)) := by
    filter_upwards [ae_restrict_mem
      (isClosed_additiveFrequencyTriangle W).measurableSet,
      hbalance] with pair hpair heq
    exact ⟨hpair, heq⟩
  have hsupport := Measure.support_subset_of_isClosed hclosed hconull
  intro pair hpair
  exact (hsupport (hfullSupport hpair)).2

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The ordered pair of child frequencies of a collision triad. -/
def childFrequencyPair (collision : ResonantThreeWaveMeasure Mode) :
    (Fin 3 -> Mode) -> Real × Real :=
  fun triad =>
    (collision.frequency (triad 1), collision.frequency (triad 2))

/-- The child-frequency-pair map is measurable. -/
theorem measurable_childFrequencyPair
    (collision : ResonantThreeWaveMeasure Mode) :
    Measurable (childFrequencyPair collision) := by
  exact (collision.measurable_frequency.comp (measurable_pi_apply 1)).prodMk
    (collision.measurable_frequency.comp (measurable_pi_apply 2))

/-- Collision mass transported to the two child-frequency coordinates. -/
def childFrequencyPairMeasure (collision : ResonantThreeWaveMeasure Mode) :
    Measure (Real × Real) :=
  Measure.map (childFrequencyPair collision) collision.collisionMeasure

/-- A continuous frequency-only weight which is balanced collision-a.e. is
linear once the child-frequency-pair measure has full relative support on the
whole additive triangle.

The first conclusion classifies the scalar profile on `[0, W]`; the second is
the corresponding pointwise classification after composition with the
collision frequency. -/
theorem continuousFrequencyProfile_linear_of_collision_ae_balance
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency : forall mode,
      collision.frequency mode ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hfullSupport : additiveFrequencyTriangle W ⊆
      ((childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W)).support) :
    exists beta : Real,
      (forall omega, omega ∈ Icc (0 : Real) W ->
        profile omega = beta * omega) ∧
      (forall mode, profile (collision.frequency mode) =
        beta * collision.frequency mode) := by
  let balanceSet : Set (Real × Real) :=
    {pair ∈ additiveFrequencyTriangle W |
      profile (pair.1 + pair.2) = profile pair.1 + profile pair.2}
  have htriad :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        childFrequencyPair collision triad ∈ balanceSet := by
    filter_upwards [collision.resonance_ae, hbalance] with
      triad hresonance hbalanced
    have hchildOne := hfrequency (triad 1)
    have hchildTwo := hfrequency (triad 2)
    have hparent := hfrequency (triad 0)
    constructor
    · exact ⟨hchildOne.1, hchildTwo.1,
        hresonance ▸ hparent.2⟩
    · simpa only [childFrequencyPair, hresonance] using hbalanced
  have hbalancePair :
      ∀ᵐ pair ∂childFrequencyPairMeasure collision, pair ∈ balanceSet := by
    have hm : AEMeasurable (childFrequencyPair collision)
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)) :=
      (measurable_childFrequencyPair collision).aemeasurable
    have hs : MeasurableSet balanceSet := by
      dsimp only [balanceSet]
      exact (isClosed_frequencyBalanceSet hprofile).measurableSet
    unfold childFrequencyPairMeasure
    exact (ae_map_iff (p := fun pair => pair ∈ balanceSet) hm
      (by simpa using hs)).2 htriad
  have hbalanceRestricted :
      ∀ᵐ pair ∂(childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W),
        profile (pair.1 + pair.2) = profile pair.1 + profile pair.2 := by
    apply ae_restrict_of_ae
    filter_upwards [hbalancePair] with pair hpair
    exact hpair.2
  have hpointwisePair :=
    continuousOn_frequencyBalance_of_ae_restrict_of_fullSupport
      hprofile hfullSupport hbalanceRestricted
  have hadd : forall x, x ∈ Icc (0 : Real) W ->
      forall y, y ∈ Icc (0 : Real) W -> x + y <= W ->
        profile (x + y) = profile x + profile y := by
    intro x hx y hy hxy
    exact hpointwisePair (x, y) ⟨hx.1, hy.1, hxy⟩
  obtain ⟨beta, hbeta⟩ :=
    continuousOn_interval_additive_linear profile hW hprofile hadd
  exact ⟨beta, hbeta, fun mode => hbeta _ (hfrequency mode)⟩

/-- The preceding pointwise theorem supplies exactly the proportionality
conclusion of `AEFrequencyBalanceRigid` for the subclass of weights which are
continuous functions of frequency. -/
theorem continuousFrequencyProfile_ae_proportional_of_collision_ae_balance
    (collision : ResonantThreeWaveMeasure Mode) {W : Real} (hW : 0 < W)
    (hfrequency : forall mode,
      collision.frequency mode ∈ Icc (0 : Real) W)
    {profile : Real -> Real}
    (hprofile : ContinuousOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ triad ∂(collision.collisionMeasure : Measure (Fin 3 -> Mode)),
        profile (collision.frequency (triad 0)) =
          profile (collision.frequency (triad 1)) +
            profile (collision.frequency (triad 2)))
    (hfullSupport : additiveFrequencyTriangle W ⊆
      ((childFrequencyPairMeasure collision).restrict
        (additiveFrequencyTriangle W)).support) :
    exists beta : Real,
      ∀ᵐ mode ∂collisionReferenceMeasure collision,
        profile (collision.frequency mode) =
          beta * collision.frequency mode := by
  obtain ⟨beta, _, hpointwise⟩ :=
    continuousFrequencyProfile_linear_of_collision_ae_balance collision hW
      hfrequency hprofile hbalance hfullSupport
  exact ⟨beta, Filter.Eventually.of_forall hpointwise⟩

end

end ArchonPhysics.ContinuousThreeWaveBalanceRigidity
