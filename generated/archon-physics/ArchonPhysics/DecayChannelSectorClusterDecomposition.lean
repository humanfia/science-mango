import ArchonPhysics.DecayChannelSectorSimultaneousCompactness

/-!
# Canonical decay-channel cluster decomposition

The simultaneous sector compactness theorem is connected back to the known
complete thermodynamic collision limit.  Along the extracted cofinal
subsequence, continuity of finite-measure addition and the exact finite-volume
partition identify the deterministic full limit with the sum of four sector
clusters.

Uniform quadratic small-ball estimates automatically remove exact-resonance
atoms from both parent--child repeated clusters.  Therefore the exact zero
atom question for the full scalar collision limit is equivalent to the same
question for only the all-distinct and child-repeated clusters.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.DecayChannelSectorClusterDecomposition

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecayChannelSectorSimultaneousCompactness
open ArchonPhysics.FiniteMeasureQuadraticSmallBallWeakLimit
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Sectorwise weak limits along one supplied cofinal subsequence recombine
to the corresponding full collision weak limit along that subsequence. -/
theorem canonicalCollisionPerSiteFiniteMeasure_decay_tendsto_along_of_sector_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (subsequence : Nat -> Nat)
    (allDistinct childRepeated parentChildOne parentChildTwo :
      FiniteMeasure Real)
    (hall : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => AllDistinctModes) (subsequence j) omega)
      atTop (nhds allDistinct))
    (hchild : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) (subsequence j) omega)
      atTop (nhds childRepeated))
    (hone : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildOneRepeated) (subsequence j) omega)
      atTop (nhds parentChildOne))
    (htwo : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildTwoRepeated) (subsequence j) omega)
      atTop (nhds parentChildTwo)) :
    Tendsto
      (fun j => canonicalCollisionPerSiteFiniteMeasure ensemble
        decayInteractionSign (subsequence j) omega)
      atTop
      (nhds (allDistinct + childRepeated + parentChildOne + parentChildTwo)) := by
  have hsum := ((hall.add hchild).add hone).add htwo
  apply hsum.congr'
  exact Eventually.of_forall fun j =>
    (canonicalCollisionPerSiteFiniteMeasure_decay_eq_sectorSum
      ensemble (subsequence j) omega).symm

/-- Every weak cluster of the first parent--child sector along an arbitrary
volume subsequence has no atom at exact resonance. -/
theorem parentChildOne_sectorWeakLimit_singleton_zero_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (subsequence : Nat -> Nat) (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildOneRepeated) (subsequence j) omega)
      atTop (nhds target)) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  apply finiteMeasure_singleton_zero_eq_zero_of_uniform_quadratic_smallBall
    (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ParentChildOneRepeated) (subsequence j) omega)
    target hlimit (5 / 8 : Real) (by norm_num)
  intro j delta hdelta hdeltaOne
  rw [canonicalDecaySector_parentChildOne_eq_iid_tail]
  exact iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure_smallBall
    ensemble omega (subsequence j + 1) hdelta hdeltaOne

/-- The same arbitrary-subsequence zero-atom theorem for the second
parent--child sector. -/
theorem parentChildTwo_sectorWeakLimit_singleton_zero_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (subsequence : Nat -> Nat) (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildTwoRepeated) (subsequence j) omega)
      atTop (nhds target)) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  apply finiteMeasure_singleton_zero_eq_zero_of_uniform_quadratic_smallBall
    (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ParentChildTwoRepeated) (subsequence j) omega)
    target hlimit (5 / 8 : Real) (by norm_num)
  intro j delta hdelta hdeltaOne
  rw [canonicalDecaySector_parentChildTwo_eq_iid_tail]
  exact iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure_smallBall
    ensemble omega (subsequence j + 1) hdelta hdeltaOne

/-- A four-sector cluster decomposition of a supplied full thermodynamic
decay collision limit. -/
structure DecaySectorClusterDecomposition
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure Real) where
  allDistinct : FiniteMeasure Real
  childRepeated : FiniteMeasure Real
  parentChildOne : FiniteMeasure Real
  parentChildTwo : FiniteMeasure Real
  subsequence : Nat -> Nat
  subsequence_strictMono : StrictMono subsequence
  allDistinct_tendsto : Tendsto
    (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => AllDistinctModes) (subsequence j) omega)
    atTop (nhds allDistinct)
  childRepeated_tendsto : Tendsto
    (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ChildRepeated) (subsequence j) omega)
    atTop (nhds childRepeated)
  parentChildOne_tendsto : Tendsto
    (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ParentChildOneRepeated) (subsequence j) omega)
    atTop (nhds parentChildOne)
  parentChildTwo_tendsto : Tendsto
    (fun j => canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
      (fun {_N} _inst => ParentChildTwoRepeated) (subsequence j) omega)
    atTop (nhds parentChildTwo)
  target_eq_sectorSum :
    target = allDistinct + childRepeated + parentChildOne + parentChildTwo
  parentChildOne_zeroAtom :
    (parentChildOne : Measure Real) ({0} : Set Real) = 0
  parentChildTwo_zeroAtom :
    (parentChildTwo : Measure Real) ({0} : Set Real) = 0

/-- Simple spectrum and the already identified complete collision limit
produce a fully aligned four-sector cluster decomposition. -/
theorem exists_decaySectorClusterDecomposition_of_simple_of_fullLimit
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure Real)
    (hsimple : forall n,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 2) omega)))
    (hfull : Tendsto
      (fun n => canonicalCollisionPerSiteFiniteMeasure ensemble
        decayInteractionSign n omega)
      atTop (nhds target)) :
    Nonempty (DecaySectorClusterDecomposition ensemble omega target) := by
  obtain ⟨allDistinct, childRepeated, parentChildOne, parentChildTwo,
      subsequence, hmono, hall, hchild, hone, htwo⟩ :=
    exists_simultaneous_decaySector_weaklyConvergent_subsequence_of_simple
      ensemble omega hsimple
  have hsector :=
    canonicalCollisionPerSiteFiniteMeasure_decay_tendsto_along_of_sector_tendsto
      ensemble omega subsequence allDistinct childRepeated parentChildOne
      parentChildTwo hall hchild hone htwo
  have hfullSub : Tendsto
      (fun j => canonicalCollisionPerSiteFiniteMeasure ensemble
        decayInteractionSign (subsequence j) omega)
      atTop (nhds target) :=
    hfull.comp hmono.tendsto_atTop
  have htarget : target =
      allDistinct + childRepeated + parentChildOne + parentChildTwo :=
    tendsto_nhds_unique hfullSub hsector
  exact ⟨{
    allDistinct := allDistinct
    childRepeated := childRepeated
    parentChildOne := parentChildOne
    parentChildTwo := parentChildTwo
    subsequence := subsequence
    subsequence_strictMono := hmono
    allDistinct_tendsto := hall
    childRepeated_tendsto := hchild
    parentChildOne_tendsto := hone
    parentChildTwo_tendsto := htwo
    target_eq_sectorSum := htarget
    parentChildOne_zeroAtom :=
      parentChildOne_sectorWeakLimit_singleton_zero_eq_zero
        ensemble omega subsequence parentChildOne hone
    parentChildTwo_zeroAtom :=
      parentChildTwo_sectorWeakLimit_singleton_zero_eq_zero
        ensemble omega subsequence parentChildTwo htwo }⟩

/-- For a canonical decomposition, the full exact-resonance atom vanishes
iff the all-distinct and child-repeated atoms both vanish. -/
theorem DecaySectorClusterDecomposition.target_zeroAtom_iff
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition ensemble omega target) :
    (target : Measure Real) ({0} : Set Real) = 0 ↔
      (cluster.allDistinct : Measure Real) ({0} : Set Real) = 0 ∧
      (cluster.childRepeated : Measure Real) ({0} : Set Real) = 0 := by
  have hEval := congrArg
    (fun mu : FiniteMeasure Real => (mu : Measure Real) ({0} : Set Real))
    cluster.target_eq_sectorSum
  calc
    (target : Measure Real) ({0} : Set Real) = 0 <->
        ((cluster.allDistinct + cluster.childRepeated +
          cluster.parentChildOne + cluster.parentChildTwo : FiniteMeasure Real) :
          Measure Real) ({0} : Set Real) = 0 := by rw [hEval]
    _ <-> (cluster.allDistinct : Measure Real) ({0} : Set Real) = 0 /\
        (cluster.childRepeated : Measure Real) ({0} : Set Real) = 0 := by
      simp [Measure.add_apply, cluster.parentChildOne_zeroAtom,
        cluster.parentChildTwo_zeroAtom]

/-- For the frozen canonical iid ensemble, the deterministic scalar decay
collision limit admits such a four-sector decomposition almost surely. -/
theorem exists_canonicalDecaySectorClusterDecomposition_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Nonempty (DecaySectorClusterDecomposition
        canonicalIIDMassPhaseEnsemble omega
        (canonicalCollisionPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble decayInteractionSign)) := by
  filter_upwards
    [canonicalPositiveVolumes_simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble,
    canonicalCollisionPerSiteFiniteMeasure_tendsto_limit_ae
      canonicalIIDMassPhaseEnsemble decayInteractionSign]
      with omega hsimple hfull
  have hsimple' : forall n,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := n + 2) omega)) := by
    intro n
    simpa [Nat.add_assoc] using hsimple (n + 1) (by omega)
  have hfull' : Tendsto
      (fun n => canonicalCollisionPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble decayInteractionSign n omega)
      atTop
      (nhds (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign)) :=
    (tendsto_add_atTop_iff_nat 1).mp hfull
  exact exists_decaySectorClusterDecomposition_of_simple_of_fullLimit
    canonicalIIDMassPhaseEnsemble omega
    (canonicalCollisionPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble decayInteractionSign)
    hsimple' hfull'

end

end ArchonPhysics.DecayChannelSectorClusterDecomposition
