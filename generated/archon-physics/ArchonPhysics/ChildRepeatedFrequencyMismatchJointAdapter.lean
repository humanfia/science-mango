import ArchonPhysics.ChildRepeatedFrequencyMismatchJointDomination

/-!
# Raw and marked adapters for child-repeated frequency--mismatch coordinates

The child-repeated sector is supported on triples of the form
`(omega_parent, omega_child, omega_child)`.  This file identifies the raw
and rank-marked `(leg frequency, decay mismatch)` laws with the genuine
two-dimensional linear equivalences from
`ChildRepeatedFrequencyMismatchJointDomination`.

For the parent leg the inverse-Jacobian factor is exactly `1 / 2`; for each
repeated child leg it is exactly `1`.  Consequently a reduced planar bound
by `C * volume` gives time-uniform broadened marginal bounds `C / 2` and `C`.
The canonical finite-volume marked laws are atomic, so their exact map
identities are unconditional while domination is stated only from the
corresponding reduced-law domination hypothesis.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.ChildRepeatedFrequencyMismatchJointAdapter

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalChildRepeatedAnnealedSectorBridge
open ArchonPhysics.CanonicalOnShellFrequencyMarginalBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.ChildRepeatedFrequencyMismatchJointDomination
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.FrequencyMismatchKernelMarginalDomination
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory

noncomputable section

/-! ## Raw frequency-triple adapter -/

/-- Raw `(leg frequency, decay mismatch)` coordinates on an unmarked
frequency triple. -/
def childRepeatedPlainFrequencyMismatchCoordinates (leg : Fin 3)
    (frequency : Fin 3 → Real) : Real × Real :=
  frequencyMismatchCoordinates (fun value ↦ value leg)
    (frequencyTripleMismatch decayInteractionSign) frequency

theorem measurable_childRepeatedPlainFrequencyMismatchCoordinates
    (leg : Fin 3) :
    Measurable (childRepeatedPlainFrequencyMismatchCoordinates leg) := by
  unfold childRepeatedPlainFrequencyMismatchCoordinates
  apply measurable_frequencyMismatchCoordinates
  · fun_prop
  · exact measurable_frequencyTripleMismatch decayInteractionSign

/-- On the child diagonal, the raw coordinates are exactly the invertible
linear coordinates on `(omega_parent, omega_child)`. -/
theorem childRepeatedPlainFrequencyMismatchCoordinates_diagonalLift
    (leg : Fin 3) (frequency : Real × Real) :
    childRepeatedPlainFrequencyMismatchCoordinates leg
        (childRepeatedFrequencyDiagonalLift frequency) =
      childRepeatedLegFrequencyMismatchLinearEquiv leg frequency := by
  rw [childRepeatedLegFrequencyMismatchLinearEquiv_apply]
  apply Prod.ext
  · rfl
  · exact frequencyTripleMismatch_decay_diagonalLift frequency

/-- Any raw law carried by the child diagonal has the same joint pushforward
as its reduced parent/child law followed by the genuine leg equivalence. -/
theorem map_childRepeatedPlainFrequencyMismatchCoordinates_eq_map_reduced_of_support
    (measure : Measure (Fin 3 → Real))
    (hsupport : measure (childRepeatedFrequencyDiagonalᶜ) = 0)
    (leg : Fin 3) :
    Measure.map (childRepeatedPlainFrequencyMismatchCoordinates leg) measure =
      Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (Measure.map childRepeatedFrequencyProjection measure) := by
  calc
    Measure.map (childRepeatedPlainFrequencyMismatchCoordinates leg) measure =
        Measure.map (childRepeatedPlainFrequencyMismatchCoordinates leg)
          (Measure.map childRepeatedFrequencyDiagonalLift
            (Measure.map childRepeatedFrequencyProjection measure)) := by
      rw [map_diagonalLift_map_projection_eq_of_compl_diagonal_eq_zero
        measure hsupport]
    _ = Measure.map
        (childRepeatedPlainFrequencyMismatchCoordinates leg ∘
          childRepeatedFrequencyDiagonalLift)
        (Measure.map childRepeatedFrequencyProjection measure) := by
      rw [Measure.map_map
        (measurable_childRepeatedPlainFrequencyMismatchCoordinates leg)
        measurable_childRepeatedFrequencyDiagonalLift]
    _ = Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (Measure.map childRepeatedFrequencyProjection measure) := by
      apply Measure.map_congr
      filter_upwards [] with frequency
      exact
        childRepeatedPlainFrequencyMismatchCoordinates_diagonalLift
          leg frequency

/-- Exact deterministic raw-to-pair identification at every finite volume. -/
theorem map_perSiteChildRepeatedPlainFrequencyMismatchCoordinates_eq_pair
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (leg : Fin 3) :
    Measure.map (childRepeatedPlainFrequencyMismatchCoordinates leg)
        (perSitePositiveWeightedFrequencyTripleMeasureWhere
          mass ChildRepeated) =
      Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (childRepeatedReducedPerSitePairMeasure mass) := by
  have hsupport :
      perSitePositiveWeightedFrequencyTripleMeasureWhere mass ChildRepeated
        (childRepeatedFrequencyDiagonalᶜ) = 0 :=
    perSiteChildRepeatedFiniteMeasure_compl_diagonal_eq_zero mass
  have hmap :=
    map_childRepeatedPlainFrequencyMismatchCoordinates_eq_map_reduced_of_support
      (perSitePositiveWeightedFrequencyTripleMeasureWhere mass ChildRepeated)
      hsupport leg
  rw [map_perSiteChildRepeatedFrequencyMeasure_eq_pairMeasure] at hmap
  exact hmap

/-! ## Actual two-mass source adapter -/

/-- For one frozen environment and one repeated parent/child mode pair, the
raw mass-pair source in `(leg frequency, mismatch)` coordinates is exactly
the leg linear-equivalence pushforward of the actual conditional reduced
frequency law. -/
theorem map_actualTwoMassChildRepeatedPairSource_joint_eq_reduced
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (modes : ChildRepeatedModePair N)
    (weight : Real × Real → ENNReal) (leg : Fin 3) :
    Measure.map
        (frequencyMismatchCoordinates
          (childRepeatedLegFrequency leg ∘
            actualTwoMassChildFrequencyChart
              fixed site₁ site₂ modes.1 modes.2)
          (childRepeatedDecayMismatch ∘
            actualTwoMassChildFrequencyChart
              fixed site₁ site₂ modes.1 modes.2))
        (iidMassPairLaw.withDensity weight) =
      Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (actualTwoMassChildRepeatedConditionalPairMeasure
          fixed site₁ site₂ modes weight) := by
  unfold actualTwoMassChildRepeatedConditionalPairMeasure
  rw [Measure.map_map
    (measurable_childRepeatedLegFrequencyMismatchLinearEquiv leg)
    (continuous_actualTwoMassChildFrequencyChart
      fixed site₁ site₂ modes.1 modes.2).measurable]
  apply Measure.map_congr
  filter_upwards [] with point
  exact (childRepeatedLegFrequencyMismatchLinearEquiv_apply leg _).symm

/-- A planar bound for one actual conditional pair law gives the exact
`C / 2` raw joint bound on the parent leg already at the mass-pair source. -/
theorem map_actualTwoMassChildRepeatedPairSource_parent_joint_le_volume
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (modes : ChildRepeatedModePair N)
    (weight : Real × Real → ENNReal) (C : ENNReal)
    (hreduced :
      actualTwoMassChildRepeatedConditionalPairMeasure
          fixed site₁ site₂ modes weight ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map
        (frequencyMismatchCoordinates
          (childRepeatedLegFrequency 0 ∘
            actualTwoMassChildFrequencyChart
              fixed site₁ site₂ modes.1 modes.2)
          (childRepeatedDecayMismatch ∘
            actualTwoMassChildFrequencyChart
              fixed site₁ site₂ modes.1 modes.2))
        (iidMassPairLaw.withDensity weight) ≤
      (C / 2) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  rw [map_actualTwoMassChildRepeatedPairSource_joint_eq_reduced]
  simpa [childRepeatedLegLebesgueConstant, div_eq_mul_inv] using
    map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
      (actualTwoMassChildRepeatedConditionalPairMeasure
        fixed site₁ site₂ modes weight) 0 C hreduced

/-- The same actual source has the exact unit-Jacobian raw joint bound on
either of the two repeated child legs. -/
theorem map_actualTwoMassChildRepeatedPairSource_child_joint_le_volume
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (modes : ChildRepeatedModePair N)
    (weight : Real × Real → ENNReal) (leg : Fin 3) (hleg : leg ≠ 0)
    (C : ENNReal)
    (hreduced :
      actualTwoMassChildRepeatedConditionalPairMeasure
          fixed site₁ site₂ modes weight ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map
        (frequencyMismatchCoordinates
          (childRepeatedLegFrequency leg ∘
            actualTwoMassChildFrequencyChart
              fixed site₁ site₂ modes.1 modes.2)
          (childRepeatedDecayMismatch ∘
            actualTwoMassChildFrequencyChart
              fixed site₁ site₂ modes.1 modes.2))
        (iidMassPairLaw.withDensity weight) ≤
      C • ((volume : Measure Real).prod (volume : Measure Real)) := by
  rw [map_actualTwoMassChildRepeatedPairSource_joint_eq_reduced]
  simpa [childRepeatedLegLebesgueConstant, hleg] using
    map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
      (actualTwoMassChildRepeatedConditionalPairMeasure
        fixed site₁ site₂ modes weight) leg C hreduced

/-! ## Rank-marked adapter -/

/-- Marked `(leg frequency, decay mismatch)` coordinates used by the
finite-time resonance kernel. -/
def childRepeatedMarkedFrequencyMismatchCoordinates (leg : Fin 3)
    (marks : Fin 3 → RankFrequencyMark) : Real × Real :=
  frequencyMismatchCoordinates (markedLegFrequency leg)
    (markedFrequencyMismatch decayInteractionSign) marks

theorem measurable_childRepeatedMarkedFrequencyMismatchCoordinates
    (leg : Fin 3) :
    Measurable (childRepeatedMarkedFrequencyMismatchCoordinates leg) := by
  unfold childRepeatedMarkedFrequencyMismatchCoordinates
  exact measurable_frequencyMismatchCoordinates
    (measurable_markedLegFrequency leg)
    (measurable_markedFrequencyMismatch decayInteractionSign)

theorem childRepeatedPlainFrequencyMismatchCoordinates_comp_forget_eq_marked
    (leg : Fin 3) :
    childRepeatedPlainFrequencyMismatchCoordinates leg ∘
        forgetRankFrequencyTriple =
      childRepeatedMarkedFrequencyMismatchCoordinates leg := by
  funext marks
  apply Prod.ext
  · rfl
  · change frequencyTripleMismatch decayInteractionSign
        (forgetRankFrequencyTriple marks) =
      markedFrequencyMismatch decayInteractionSign marks
    rw [ArchonPhysics.CanonicalOnShellMarkedCluster.markedFrequencyMismatch_decay_eq]
    unfold frequencyTripleMismatch
    rw [Fin.sum_univ_three]
    simp [decayInteractionSign, forgetRankFrequencyTriple]
    ring

/-- A marked law whose forgotten frequency law is carried by the child
diagonal maps exactly to the leg equivalence applied to its reduced law. -/
theorem map_childRepeatedMarkedFrequencyMismatchCoordinates_eq_map_reduced_of_support
    (measure : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hsupport :
      (measure.map forgetRankFrequencyTriple : Measure (Fin 3 → Real))
        (childRepeatedFrequencyDiagonalᶜ) = 0)
    (leg : Fin 3) :
    Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates leg)
        (measure : Measure (Fin 3 → RankFrequencyMark)) =
      Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (Measure.map childRepeatedFrequencyProjection
          (Measure.map forgetRankFrequencyTriple (measure : Measure _))) := by
  rw [←
    childRepeatedPlainFrequencyMismatchCoordinates_comp_forget_eq_marked]
  rw [← Measure.map_map
    (measurable_childRepeatedPlainFrequencyMismatchCoordinates leg)
    measurable_forgetRankFrequencyTriple]
  exact
    map_childRepeatedPlainFrequencyMismatchCoordinates_eq_map_reduced_of_support
      (Measure.map forgetRankFrequencyTriple (measure : Measure _))
      (by simpa only [FiniteMeasure.toMeasure_map] using hsupport) leg

/-- Exact canonical finite-volume marked raw law in genuine joint
coordinates.  The right side is the existing pair-indexed deterministic
child-repeated law. -/
theorem map_canonicalChildRepeatedMarkedPerSite_joint_eq_pair
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (leg : Fin 3) :
    Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates leg)
        (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          ensemble n omega : Measure (Fin 3 → RankFrequencyMark)) =
      Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (childRepeatedReducedPerSitePairMeasure
          (ensemble.restrictPositiveMass (N := n + 2) omega)) := by
  have hsupport :
      ((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          ensemble n omega).map forgetRankFrequencyTriple :
        Measure (Fin 3 → Real))
          (childRepeatedFrequencyDiagonalᶜ) = 0 := by
    rw [map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank]
    exact perSiteChildRepeatedFiniteMeasure_compl_diagonal_eq_zero
      (ensemble.restrictPositiveMass (N := n + 2) omega)
  rw [map_childRepeatedMarkedFrequencyMismatchCoordinates_eq_map_reduced_of_support
    (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
      ensemble n omega) hsupport leg]
  rw [show
    Measure.map forgetRankFrequencyTriple
        (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          ensemble n omega : Measure (Fin 3 → RankFrequencyMark)) =
      (canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
          ensemble n omega : Measure (Fin 3 → Real)) by
    simpa only [FiniteMeasure.toMeasure_map] using congrArg
      (fun measure : FiniteMeasure (Fin 3 → Real) ↦
        (measure : Measure (Fin 3 → Real)))
      (map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank
        ensemble n omega)]
  exact congrArg
    (Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg))
    (map_perSiteChildRepeatedFrequencyMeasure_eq_pairMeasure
      (ensemble.restrictPositiveMass (N := n + 2) omega))

/-! ## Exact connection to the canonical scalar sector -/

/-- At every finite volume, the canonical scalar child-repeated decay sector
is the mismatch (`Prod.snd`) marginal of the marked raw joint law, for every
choice of observed leg. -/
theorem map_snd_canonicalChildRepeatedMarkedPerSite_joint_eq_decaySector
    (n : Nat) (omega : RandomEnsemble.SampleSpace) (leg : Fin 3) :
    Measure.map Prod.snd
        (Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates leg)
          (canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
            canonicalIIDMassPhaseEnsemble n omega :
              Measure (Fin 3 → RankFrequencyMark))) =
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst ↦ ChildRepeated) n omega : Measure Real) := by
  rw [map_canonicalChildRepeatedMarkedPerSite_joint_eq_pair]
  rw [Measure.map_map measurable_snd
    (measurable_childRepeatedLegFrequencyMismatchLinearEquiv leg)]
  have hcoordinate :
      Prod.snd ∘ childRepeatedLegFrequencyMismatchLinearEquiv leg =
        childRepeatedDecayMismatch := by
    funext frequency
    exact congrArg Prod.snd
      (childRepeatedLegFrequencyMismatchLinearEquiv_apply leg frequency)
  rw [hcoordinate]
  have hsector := canonicalChildRepeatedReducedPerSite_map_decay_eq_sector
    n omega
  rw [map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank]
    at hsector
  have hsectorMeasure := congrArg
    (fun measure : FiniteMeasure Real ↦ (measure : Measure Real)) hsector
  simp only [FiniteMeasure.toMeasure_map] at hsectorMeasure
  change
    (Measure.map childRepeatedDecayMismatch
      (Measure.map childRepeatedFrequencyProjection
        (perSitePositiveWeightedFrequencyTripleMeasureWhere
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := n + 2) omega) ChildRepeated))) = _ at hsectorMeasure
  rw [map_perSiteChildRepeatedFrequencyMeasure_eq_pairMeasure]
    at hsectorMeasure
  exact hsectorMeasure

/-- The annealed canonical scalar child-repeated sector is likewise the
second marginal of every genuine leg joint law on the reduced plane. -/
theorem map_snd_canonicalChildRepeatedReducedAnnealed_joint_eq_decaySector
    (n : Nat) (leg : Fin 3) :
    Measure.map Prod.snd
        (Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
          (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
            Measure (Real × Real))) =
      (canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst ↦ ChildRepeated) n : Measure Real) := by
  rw [Measure.map_map measurable_snd
    (measurable_childRepeatedLegFrequencyMismatchLinearEquiv leg)]
  have hcoordinate :
      Prod.snd ∘ childRepeatedLegFrequencyMismatchLinearEquiv leg =
        childRepeatedDecayMismatch := by
    funext frequency
    exact congrArg Prod.snd
      (childRepeatedLegFrequencyMismatchLinearEquiv_apply leg frequency)
  rw [hcoordinate]
  simpa only [FiniteMeasure.toMeasure_map] using congrArg
    (fun measure : FiniteMeasure Real ↦ (measure : Measure Real))
    (canonicalDecaySectorAnnealed_childRepeated_eq_map_reduced n).symm

/-! ## Generic marked joint and broadened marginal domination -/

/-- Exact leg-dependent joint domination for a marked child-diagonal law. -/
theorem map_childRepeatedMarkedFrequencyMismatchCoordinates_le_volume_of_support
    (measure : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hsupport :
      (measure.map forgetRankFrequencyTriple : Measure (Fin 3 → Real))
        (childRepeatedFrequencyDiagonalᶜ) = 0)
    (leg : Fin 3) (C : ENNReal)
    (hreduced :
      (Measure.map childRepeatedFrequencyProjection
        (Measure.map forgetRankFrequencyTriple (measure : Measure _))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates leg)
        (measure : Measure (Fin 3 → RankFrequencyMark)) ≤
      (C * childRepeatedLegLebesgueConstant leg) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  rw [map_childRepeatedMarkedFrequencyMismatchCoordinates_eq_map_reduced_of_support
    measure hsupport leg]
  exact map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
    _ leg C hreduced

/-- The kernel marginal theorem turns the preceding joint estimate into a
bound uniform in every positive broadening time. -/
theorem map_childRepeatedMarkedLeg_broadenedResonanceMeasure_le_volume_of_support
    (measure : FiniteMeasure (Fin 3 → RankFrequencyMark))
    (hsupport :
      (measure.map forgetRankFrequencyTriple : Measure (Fin 3 → Real))
        (childRepeatedFrequencyDiagonalᶜ) = 0)
    {T : Real} (hT : 0 < T) (leg : Fin 3) (C : ENNReal)
    (hreduced :
      (Measure.map childRepeatedFrequencyProjection
        (Measure.map forgetRankFrequencyTriple (measure : Measure _))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (markedLegFrequency leg)
        (broadenedResonanceMeasure measure
          (markedFrequencyMismatch decayInteractionSign)
          (measurable_markedFrequencyMismatch decayInteractionSign)
          T hT : Measure (Fin 3 → RankFrequencyMark)) ≤
      (C * childRepeatedLegLebesgueConstant leg) •
        (volume : Measure Real) := by
  apply map_frequency_broadenedResonanceMeasure_le_volume_of_joint_le
    measure
    (measurable_markedFrequencyMismatch decayInteractionSign)
    hT (markedLegFrequency leg) (measurable_markedLegFrequency leg)
    (C * childRepeatedLegLebesgueConstant leg)
  exact
    map_childRepeatedMarkedFrequencyMismatchCoordinates_le_volume_of_support
      measure hsupport leg C hreduced

/-! ## Hybrid-lift endpoints with explicit parent/child constants -/

theorem ChildRepeatedScalarClusterHybridLiftData.parent_joint_le_volume
    {Omega : Type*} [MeasurableSpace Omega]
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (C : ENNReal)
    (hreduced :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates 0)
        (lift.markedTarget : Measure (Fin 3 → RankFrequencyMark)) ≤
      (C / 2) • ((volume : Measure Real).prod (volume : Measure Real)) := by
  simpa [childRepeatedLegLebesgueConstant, div_eq_mul_inv] using
    map_childRepeatedMarkedFrequencyMismatchCoordinates_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal 0 C
        (by simpa only [FiniteMeasure.toMeasure_map] using hreduced)

theorem ChildRepeatedScalarClusterHybridLiftData.childOne_joint_le_volume
    {Omega : Type*} [MeasurableSpace Omega]
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (C : ENNReal)
    (hreduced :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates 1)
        (lift.markedTarget : Measure (Fin 3 → RankFrequencyMark)) ≤
      C • ((volume : Measure Real).prod (volume : Measure Real)) := by
  simpa [childRepeatedLegLebesgueConstant] using
    map_childRepeatedMarkedFrequencyMismatchCoordinates_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal 1 C
        (by simpa only [FiniteMeasure.toMeasure_map] using hreduced)

theorem ChildRepeatedScalarClusterHybridLiftData.childTwo_joint_le_volume
    {Omega : Type*} [MeasurableSpace Omega]
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (C : ENNReal)
    (hreduced :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates 2)
        (lift.markedTarget : Measure (Fin 3 → RankFrequencyMark)) ≤
      C • ((volume : Measure Real).prod (volume : Measure Real)) := by
  simpa [childRepeatedLegLebesgueConstant] using
    map_childRepeatedMarkedFrequencyMismatchCoordinates_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal 2 C
        (by simpa only [FiniteMeasure.toMeasure_map] using hreduced)

theorem ChildRepeatedScalarClusterHybridLiftData.parent_broadened_le_volume
    {Omega : Type*} [MeasurableSpace Omega]
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hreduced :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (markedLegFrequency 0)
        (broadenedResonanceMeasure lift.markedTarget
          (markedFrequencyMismatch decayInteractionSign)
          (measurable_markedFrequencyMismatch decayInteractionSign)
          T hT : Measure (Fin 3 → RankFrequencyMark)) ≤
      (C / 2) • (volume : Measure Real) := by
  simpa [childRepeatedLegLebesgueConstant, div_eq_mul_inv] using
    map_childRepeatedMarkedLeg_broadenedResonanceMeasure_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal hT 0 C
        (by simpa only [FiniteMeasure.toMeasure_map] using hreduced)

theorem ChildRepeatedScalarClusterHybridLiftData.childOne_broadened_le_volume
    {Omega : Type*} [MeasurableSpace Omega]
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hreduced :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (markedLegFrequency 1)
        (broadenedResonanceMeasure lift.markedTarget
          (markedFrequencyMismatch decayInteractionSign)
          (measurable_markedFrequencyMismatch decayInteractionSign)
          T hT : Measure (Fin 3 → RankFrequencyMark)) ≤
      C • (volume : Measure Real) := by
  simpa [childRepeatedLegLebesgueConstant] using
    map_childRepeatedMarkedLeg_broadenedResonanceMeasure_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal hT 1 C
        (by simpa only [FiniteMeasure.toMeasure_map] using hreduced)

theorem ChildRepeatedScalarClusterHybridLiftData.childTwo_broadened_le_volume
    {Omega : Type*} [MeasurableSpace Omega]
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hreduced :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (markedLegFrequency 2)
        (broadenedResonanceMeasure lift.markedTarget
          (markedFrequencyMismatch decayInteractionSign)
          (measurable_markedFrequencyMismatch decayInteractionSign)
          T hT : Measure (Fin 3 → RankFrequencyMark)) ≤
      C • (volume : Measure Real) := by
  simpa [childRepeatedLegLebesgueConstant] using
    map_childRepeatedMarkedLeg_broadenedResonanceMeasure_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal hT 2 C
        (by simpa only [FiniteMeasure.toMeasure_map] using hreduced)

/-! ## Canonical annealed reduced-law endpoints -/

theorem canonicalChildRepeatedReducedAnnealed_parent_joint_le_volume
    (n : Nat) (C : ENNReal)
    (hreduced :
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
        Measure (Real × Real)) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv 0)
        (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
          Measure (Real × Real)) ≤
      (C / 2) • ((volume : Measure Real).prod (volume : Measure Real)) := by
  simpa [childRepeatedLegLebesgueConstant, div_eq_mul_inv] using
    map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
        Measure (Real × Real)) 0 C hreduced

theorem canonicalChildRepeatedReducedAnnealed_child_joint_le_volume
    (n : Nat) (leg : Fin 3) (hleg : leg ≠ 0) (C : ENNReal)
    (hreduced :
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
        Measure (Real × Real)) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
          Measure (Real × Real)) ≤
      C • ((volume : Measure Real).prod (volume : Measure Real)) := by
  simpa [childRepeatedLegLebesgueConstant, hleg] using
    map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
        Measure (Real × Real)) leg C hreduced

theorem canonicalChildRepeatedReducedAnnealed_parent_broadened_le_volume
    (n : Nat) {T : Real} (hT : 0 < T) (C : ENNReal)
    (hreduced :
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
        Measure (Real × Real)) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedLegFrequency 0)
        (broadenedResonanceMeasure
          (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n)
          childRepeatedDecayMismatch measurable_childRepeatedDecayMismatch
          T hT : Measure (Real × Real)) ≤
      (C / 2) • (volume : Measure Real) := by
  simpa [childRepeatedLegLebesgueConstant, div_eq_mul_inv] using
    map_childRepeatedLegFrequency_broadenedResonanceMeasure_le_volume
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n)
      hT 0 C hreduced

theorem canonicalChildRepeatedReducedAnnealed_child_broadened_le_volume
    (n : Nat) {T : Real} (hT : 0 < T)
    (leg : Fin 3) (hleg : leg ≠ 0) (C : ENNReal)
    (hreduced :
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
        Measure (Real × Real)) ≤
        C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedLegFrequency leg)
        (broadenedResonanceMeasure
          (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n)
          childRepeatedDecayMismatch measurable_childRepeatedDecayMismatch
          T hT : Measure (Real × Real)) ≤
      C • (volume : Measure Real) := by
  simpa [childRepeatedLegLebesgueConstant, hleg] using
    map_childRepeatedLegFrequency_broadenedResonanceMeasure_le_volume
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n)
      hT leg C hreduced

end

end ArchonPhysics.ChildRepeatedFrequencyMismatchJointAdapter
