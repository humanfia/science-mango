import ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
import ArchonPhysics.DecayChannelSectorClusterOnShellRecombination

/-!
# Full decay broadened-mass upper bounds from only the two main sectors

The all-distinct and child-repeated scalar cluster measures may be treated by
Lebesgue domination.  The two parent--child sectors need no raw density:
their already proved uniform `O(T^{-1/2})` broadened bounds are enough.  This
module recombines those facts into the eventual full-law mass ceiling needed
by the positive on-shell cluster construction.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.CanonicalDecayMainSectorBroadenedMassUpper

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelParentChildClusterBroadeningDecay
open ArchonPhysics.DecayChannelSectorClusterDecomposition
open ArchonPhysics.DecayChannelSectorClusterOnShellRecombination
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open Filter MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- At every positive time, separate Lebesgue ceilings for the two main
sectors and the genuine parent--child fractional estimates give an explicit
upper bound for the complete decay cluster. -/
theorem DecaySectorClusterDecomposition.target_broadened_mass_le_of_mainSectorDomination
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition ensemble omega target)
    (allDistinctConstant childRepeatedConstant : NNReal)
    (hallDistinct : (cluster.allDistinct : Measure Real) ≤
      allDistinctConstant • (volume : Measure Real))
    (hchildRepeated : (cluster.childRepeated : Measure Real) ≤
      childRepeatedConstant • (volume : Measure Real))
    {T : Real} (hT : 0 < T) :
    ((broadenedResonanceMeasure target id measurable_id T hT).mass : Real) ≤
      (allDistinctConstant : Real) + (childRepeatedConstant : Real) +
        5 / (2 * Real.pi * Real.sqrt T) +
        5 / (2 * Real.pi * Real.sqrt T) := by
  have hallMass :
      ((broadenedResonanceMeasure cluster.allDistinct id measurable_id
        T hT).mass : Real) ≤ (allDistinctConstant : Real) :=
    broadenedResonanceMeasure_mass_le_of_le_smul_volume
      cluster.allDistinct allDistinctConstant hallDistinct hT
  have hchildMass :
      ((broadenedResonanceMeasure cluster.childRepeated id measurable_id
        T hT).mass : Real) ≤ (childRepeatedConstant : Real) :=
    broadenedResonanceMeasure_mass_le_of_le_smul_volume
      cluster.childRepeated childRepeatedConstant hchildRepeated hT
  have honeLimit : Tendsto
      (fun n ↦ iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (cluster.subsequence n + 1))
      atTop (nhds cluster.parentChildOne) := by
    simpa only [canonicalDecaySector_parentChildOne_eq_iid_tail] using
      cluster.parentChildOne_tendsto
  have htwoLimit : Tendsto
      (fun n ↦ iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (cluster.subsequence n + 1))
      atTop (nhds cluster.parentChildTwo) := by
    simpa only [canonicalDecaySector_parentChildTwo_eq_iid_tail] using
      cluster.parentChildTwo_tendsto
  have honeMass :
      ((broadenedResonanceMeasure cluster.parentChildOne id measurable_id
        T hT).mass : Real) ≤ 5 / (2 * Real.pi * Real.sqrt T) :=
    parentChildOne_weakLimit_broadened_mass_le
      ensemble omega (fun n ↦ cluster.subsequence n + 1)
      cluster.parentChildOne honeLimit hT
  have htwoMass :
      ((broadenedResonanceMeasure cluster.parentChildTwo id measurable_id
        T hT).mass : Real) ≤ 5 / (2 * Real.pi * Real.sqrt T) :=
    parentChildTwo_weakLimit_broadened_mass_le
      ensemble omega (fun n ↦ cluster.subsequence n + 1)
      cluster.parentChildTwo htwoLimit hT
  rw [ArchonPhysics.DecayChannelSectorClusterOnShellRecombination.DecaySectorClusterDecomposition.target_broadened_mass_eq_sectorSum cluster T hT]
  exact add_le_add (add_le_add (add_le_add hallMass hchildMass) honeMass)
    htwoMass

/-- Along every diverging positive observation-time path, the complete decay
broadened mass is eventually bounded by `C_all + C_child + 1`.  The extra
unit absorbs both singular parent--child sectors after their unconditional
on-shell decay.  The conclusion is in `NNReal`, exactly the shape consumed by
the canonical positive-cluster upper premise. -/
theorem DecaySectorClusterDecomposition.eventually_target_broadened_mass_le_mainConstants_add_one
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition ensemble omega target)
    (allDistinctConstant childRepeatedConstant : NNReal)
    (hallDistinct : (cluster.allDistinct : Measure Real) ≤
      allDistinctConstant • (volume : Measure Real))
    (hchildRepeated : (cluster.childRepeated : Measure Real) ≤
      childRepeatedConstant • (volume : Measure Real))
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    ∀ᶠ n in atTop,
      (broadenedResonanceMeasure target id measurable_id
          (time n) (htime_pos n)).mass ≤
        allDistinctConstant + childRepeatedConstant + 1 := by
  have hparent := ArchonPhysics.DecayChannelParentChildClusterBroadeningDecay.DecaySectorClusterDecomposition.parentChild_broadened_mass_tendsto_zero cluster
    time htime_pos htime
  have hparentEventually : ∀ᶠ n in atTop,
      ((broadenedResonanceMeasure cluster.parentChildOne id measurable_id
          (time n) (htime_pos n)).mass : Real) +
        ((broadenedResonanceMeasure cluster.parentChildTwo id measurable_id
          (time n) (htime_pos n)).mass : Real) ≤ 1 := by
    filter_upwards [(tendsto_order.1 hparent).2 (1 : Real) zero_lt_one]
      with n hn
    exact hn.le
  filter_upwards [hparentEventually] with n hparentBound
  apply NNReal.coe_le_coe.mp
  rw [ArchonPhysics.DecayChannelSectorClusterOnShellRecombination.DecaySectorClusterDecomposition.target_broadened_mass_eq_sectorSum cluster
    (time n) (htime_pos n)]
  have hallMass :
      ((broadenedResonanceMeasure cluster.allDistinct id measurable_id
        (time n) (htime_pos n)).mass : Real) ≤
        (allDistinctConstant : Real) :=
    broadenedResonanceMeasure_mass_le_of_le_smul_volume
      cluster.allDistinct allDistinctConstant hallDistinct (htime_pos n)
  have hchildMass :
      ((broadenedResonanceMeasure cluster.childRepeated id measurable_id
        (time n) (htime_pos n)).mass : Real) ≤
        (childRepeatedConstant : Real) :=
    broadenedResonanceMeasure_mass_le_of_le_smul_volume
      cluster.childRepeated childRepeatedConstant hchildRepeated (htime_pos n)
  calc
    ((broadenedResonanceMeasure cluster.allDistinct id measurable_id
          (time n) (htime_pos n)).mass : Real) +
        ((broadenedResonanceMeasure cluster.childRepeated id measurable_id
          (time n) (htime_pos n)).mass : Real) +
        ((broadenedResonanceMeasure cluster.parentChildOne id measurable_id
          (time n) (htime_pos n)).mass : Real) +
        ((broadenedResonanceMeasure cluster.parentChildTwo id measurable_id
          (time n) (htime_pos n)).mass : Real) =
      (((broadenedResonanceMeasure cluster.allDistinct id measurable_id
          (time n) (htime_pos n)).mass : Real) +
        ((broadenedResonanceMeasure cluster.childRepeated id measurable_id
          (time n) (htime_pos n)).mass : Real)) +
        (((broadenedResonanceMeasure cluster.parentChildOne id measurable_id
          (time n) (htime_pos n)).mass : Real) +
        ((broadenedResonanceMeasure cluster.parentChildTwo id measurable_id
          (time n) (htime_pos n)).mass : Real)) := by ring
    _ ≤ ((allDistinctConstant : Real) +
          (childRepeatedConstant : Real)) + 1 :=
      add_le_add (add_le_add hallMass hchildMass) hparentBound
    _ = ((allDistinctConstant + childRepeatedConstant + 1 : NNReal) :
        Real) := by norm_num

/-- Canonical scalar wrapper in exactly the shape of the `hmassUpper` premise
of `exists_positive_canonicalOnShellMarkedCluster_of_inverseTimeSmallBallLower`.
No domination of the two singular parent--child raw laws is requested. -/
theorem canonicalBroadenedCollisionPerSiteMeasureLimit_eventually_mass_le_of_mainSectorDomination
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (cluster : DecaySectorClusterDecomposition ensemble omega
      (canonicalCollisionPerSiteMeasureLimit ensemble
        RandomMassThreeWaveCollisionNetwork.decayInteractionSign))
    (allDistinctConstant childRepeatedConstant : NNReal)
    (hallDistinct : (cluster.allDistinct : Measure Real) ≤
      allDistinctConstant • (volume : Measure Real))
    (hchildRepeated : (cluster.childRepeated : Measure Real) ≤
      childRepeatedConstant • (volume : Measure Real))
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    ∀ᶠ n in atTop,
      (canonicalBroadenedCollisionPerSiteMeasureLimit ensemble
          RandomMassThreeWaveCollisionNetwork.decayInteractionSign
          (time n) (htime_pos n)).mass ≤
        allDistinctConstant + childRepeatedConstant + 1 := by
  simpa only [canonicalBroadenedCollisionPerSiteMeasureLimit] using
    ArchonPhysics.CanonicalDecayMainSectorBroadenedMassUpper.DecaySectorClusterDecomposition.eventually_target_broadened_mass_le_mainConstants_add_one
      cluster allDistinctConstant childRepeatedConstant hallDistinct
      hchildRepeated time htime_pos htime

end

end ArchonPhysics.CanonicalDecayMainSectorBroadenedMassUpper
