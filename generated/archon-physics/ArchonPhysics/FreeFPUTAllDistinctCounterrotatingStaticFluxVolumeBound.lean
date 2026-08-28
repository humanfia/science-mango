import ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
import ArchonPhysics.OrderedCounterrotatingStaticFluxVolumeBound

/-!
# Linear-volume bound for the physical all-distinct counterrotating mass

The free FPUT closure is indexed by canonical quadratic phase-term
representatives at one fixed observed mode, whereas the spectral Parseval
bound is indexed by all ordered three-mode tuples.  This file supplies the
missing exact reindexing.

The representative set is first enlarged to every two-conjugate quadratic
term.  Its two input modes inject into the ordered triple whose first leg is
the fixed observed mode.  Positivity permits enlargement to every ordered
triple.  The complete spectral bound then gives an `O(N)` static mass, with no
`N^2` tuple-counting loss and no acoustic lower gap.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctCounterrotatingStaticFluxVolumeBound

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedCounterrotatingStaticFluxVolumeBound
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open scoped BigOperators

noncomputable section

/-- A physical modal-energy profile transported to ordered spectral indices. -/
def orderedEnergy {N : Nat} [NeZero N]
    (energy : Lattice.Site N → Real) (k : OrderedModeIndex N) : Real :=
  energy (orderedIndexEquiv k)

/-- The ordered triple with a fixed physical output and two supplied physical
input modes. -/
def fixedOutputOrderedTriple {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (inputModes : Fin 2 → Lattice.Site N) :
    OrderedModeTriple N :=
  fun r ↦ orderedIndexEquiv.symm
    (quadraticCollisionModes observed
      (counterrotatingQuadraticPhaseTerm inputModes) r)

/-- The symmetric missing-leg definition of the all-plus action flux is the
usual sum of its three pairwise action products. -/
theorem orderedAllPlusActionFlux_eq_pairwise
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real) (modes : OrderedModeTriple N) :
    orderedAllPlusActionFlux m energy modes =
      orderedModeAction m energy (modes 1) *
          orderedModeAction m energy (modes 2) +
        orderedModeAction m energy (modes 0) *
          orderedModeAction m energy (modes 2) +
        orderedModeAction m energy (modes 0) *
          orderedModeAction m energy (modes 1) := by
  unfold orderedAllPlusActionFlux pairActionEnvelope
  rw [Fin.sum_univ_three]
  simp only [Fin.prod_univ_three]
  simp

/-- Ordered action at the inverse image of a physical mode is exactly the
physical harmonic action. -/
theorem orderedModeAction_orderedEnergy_symm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (mode : Lattice.Site N) :
    orderedModeAction m (orderedEnergy energy) (orderedIndexEquiv.symm mode) =
      modeAction energy (modeFrequency m) mode := by
  unfold orderedModeAction orderedEnergy modeAction
  rw [orderedModeFrequency_harmonicHermitian_eq]
  simp

/-- Transporting the fixed-output ordered triple back to physical indices
recovers the collision modes of the associated counterrotating term. -/
theorem orderedIndex_fixedOutputOrderedTriple_eq_collisionModes
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    (fun r ↦ orderedIndexEquiv
      (fixedOutputOrderedTriple observed inputModes r)) =
      quadraticCollisionModes observed
        (counterrotatingQuadraticPhaseTerm inputModes) := by
  funext r
  simp [fixedOutputOrderedTriple]

/-- Positivity of the fixed-output ordered tuple is exactly physical
positive-frequency positivity of the counterrotating collision tuple. -/
theorem fixedOutputOrderedTriple_positive_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    IsPositiveOrderedTriple m
        (fixedOutputOrderedTriple observed inputModes) ↔
      PositiveModeTuple m
        (quadraticCollisionModes observed
          (counterrotatingQuadraticPhaseTerm inputModes)) := by
  rw [isPositiveOrderedTriple_iff_physical]
  rw [orderedIndex_fixedOutputOrderedTriple_eq_collisionModes]

/-- On simple spectrum, the ordered weight of the fixed-output tuple is the
physical normal-mode weight used in the FPUT representative sum. -/
theorem fixedOutput_harmonicWeight_eq_physical
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    harmonicOrderedNormalizedInteractionWeight m
        (fixedOutputOrderedTriple observed inputModes) =
      normalizedInteractionWeight m
        (quadraticCollisionModes observed
          (counterrotatingQuadraticPhaseTerm inputModes)) := by
  rw [harmonicOrderedNormalizedInteractionWeight_eq m hsimple]
  rw [orderedIndex_fixedOutputOrderedTriple_eq_collisionModes]

/-- The ordered all-plus action flux agrees exactly with the signed physical
counterrotating quadratic flux. -/
theorem fixedOutput_orderedAllPlusActionFlux_eq_physical
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    orderedAllPlusActionFlux m (orderedEnergy energy)
        (fixedOutputOrderedTriple observed inputModes) =
      quadraticSignedCollisionFlux
        (counterrotatingQuadraticPhaseTerm inputModes)
        (modeAction energy (modeFrequency m)) observed := by
  rw [orderedAllPlusActionFlux_eq_pairwise]
  have hzero := orderedModeAction_orderedEnergy_symm
    m energy (inputModes 0)
  have hone := orderedModeAction_orderedEnergy_symm
    m energy (inputModes 1)
  have hObserved := orderedModeAction_orderedEnergy_symm m energy observed
  change
    orderedModeAction m (orderedEnergy energy)
          (orderedIndexEquiv.symm (inputModes 0)) *
        orderedModeAction m (orderedEnergy energy)
          (orderedIndexEquiv.symm (inputModes 1)) +
      orderedModeAction m (orderedEnergy energy)
          (orderedIndexEquiv.symm observed) *
        orderedModeAction m (orderedEnergy energy)
          (orderedIndexEquiv.symm (inputModes 1)) +
      orderedModeAction m (orderedEnergy energy)
          (orderedIndexEquiv.symm observed) *
        orderedModeAction m (orderedEnergy energy)
          (orderedIndexEquiv.symm (inputModes 0)) = _
  rw [hzero, hone, hObserved]
  have hinput : quadraticInputInteractionSign
      (counterrotatingQuadraticPhaseTerm inputModes) = fun _ ↦ .plus := by
    funext r
    fin_cases r <;> rfl
  rw [quadraticSignedCollisionFlux, hinput,
    signedThreeWaveCollisionFlux_plus_plus]
  rfl

/-- Physical static-flux summand on one quadratic phase term. -/
def physicalCounterrotatingStaticTerm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) : Real :=
  4 * (kappa ^ 2 *
      normalizedInteractionWeight m (quadraticCollisionModes observed q)) *
    quadraticSignedCollisionFlux q
      (modeAction energy (modeFrequency m)) observed

/-- Ordered positive all-plus static summand. -/
def orderedPositiveAllPlusStaticTerm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa : Real) (energy : OrderedModeIndex N → Real)
    (modes : OrderedModeTriple N) : Real := by
  classical
  exact if IsPositiveOrderedTriple m modes then
      4 * (kappa ^ 2 * harmonicOrderedNormalizedInteractionWeight m modes) *
        orderedAllPlusActionFlux m energy modes
    else 0

/-- One counterrotating physical term equals the ordered filtered term at its
fixed-output image, including the zero-frequency branch. -/
theorem physicalCounterrotatingStaticTerm_eq_ordered
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (inputModes : Fin 2 → Lattice.Site N) :
    physicalCounterrotatingStaticTerm m kappa energy observed
        (counterrotatingQuadraticPhaseTerm inputModes) =
      orderedPositiveAllPlusStaticTerm m kappa (orderedEnergy energy)
        (fixedOutputOrderedTriple observed inputModes) := by
  unfold orderedPositiveAllPlusStaticTerm
  by_cases hpositive : IsPositiveOrderedTriple m
      (fixedOutputOrderedTriple observed inputModes)
  · rw [if_pos hpositive]
    unfold physicalCounterrotatingStaticTerm
    rw [fixedOutput_harmonicWeight_eq_physical m hsimple,
      fixedOutput_orderedAllPlusActionFlux_eq_physical]
  · rw [if_neg hpositive]
    have horderedZero :=
      harmonicOrderedNormalizedInteractionWeight_eq_zero_of_not_positive
        m (fixedOutputOrderedTriple observed inputModes) hpositive
    have hweight := fixedOutput_harmonicWeight_eq_physical
      m hsimple observed inputModes
    have hphysicalZero :
        normalizedInteractionWeight m
          (quadraticCollisionModes observed
            (counterrotatingQuadraticPhaseTerm inputModes)) = 0 := by
      rw [← hweight]
      exact horderedZero
    unfold physicalCounterrotatingStaticTerm
    rw [hphysicalZero]
    ring

/-- All two-conjugate quadratic terms, with unrestricted input modes. -/
def allCounterrotatingQuadraticPhaseTerms
    (N : Nat) [NeZero N] : Finset (QuadraticPhaseTerm N) := by
  classical
  exact Finset.univ.image counterrotatingQuadraticPhaseTerm

/-- The counterrotating constructor is injective because its first projection
recovers the two input modes. -/
theorem counterrotatingQuadraticPhaseTerm_injective {N : Nat} :
    Function.Injective
      (counterrotatingQuadraticPhaseTerm :
        (Fin 2 → Lattice.Site N) → QuadraticPhaseTerm N) := by
  intro a b h
  exact congrArg Prod.fst h

/-- Every canonical positive all-distinct counterrotating representative is
among the unrestricted two-conjugate terms. -/
theorem positiveAllDistinctCounterrotatingRepresentatives_subset_all
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    positiveAllDistinctCounterrotatingRepresentatives m observed ⊆
      allCounterrotatingQuadraticPhaseTerms N := by
  classical
  intro q hq
  have hparts :=
    (mem_positiveAllDistinctCounterrotatingRepresentatives_iff
      m observed q).1 hq
  rw [allCounterrotatingQuadraticPhaseTerms, Finset.mem_image]
  refine ⟨q.1, Finset.mem_univ _, ?_⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hparts.2.1.symm
    · exact hparts.2.2.symm

/-- Physical counterrotating static terms are nonnegative for a nonnegative
energy profile. -/
theorem physicalCounterrotatingStaticTerm_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (inputModes : Fin 2 → Lattice.Site N)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    0 ≤ physicalCounterrotatingStaticTerm m kappa energy observed
      (counterrotatingQuadraticPhaseTerm inputModes) := by
  have hcounter : CounterrotatingQuadraticRepresentative
      (counterrotatingQuadraticPhaseTerm inputModes) :=
    quadraticCollisionSign_counterrotatingQuadraticPhaseTerm inputModes
  have hflux := quadraticSignedCollisionFlux_nonneg_of_counterrotating
    m energy observed (counterrotatingQuadraticPhaseTerm inputModes)
      henergy hcounter
  unfold physicalCounterrotatingStaticTerm
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (mul_nonneg (sq_nonneg kappa)
        (normalizedInteractionWeight_nonneg m _))) hflux

/-- The fixed-output ordered embedding of input-mode pairs is injective. -/
theorem fixedOutputOrderedTriple_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    Function.Injective (fixedOutputOrderedTriple observed) := by
  intro a b h
  funext r
  have hr := congrFun h r.succ
  exact orderedIndexEquiv.symm.injective (by
    simpa [fixedOutputOrderedTriple] using hr)

/-- Ordered all-plus actions are nonnegative on positive triples when modal
energies are nonnegative. -/
theorem orderedAllPlusActionFlux_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real) (modes : OrderedModeTriple N)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (hpositive : IsPositiveOrderedTriple m modes) :
    0 ≤ orderedAllPlusActionFlux m energy modes := by
  have haction (r : Fin 3) :
      0 ≤ orderedModeAction m energy (modes r) := by
    exact div_nonneg (henergy (modes r))
      ((mem_orderedPositiveModeIndices_iff m (modes r)).1
        (hpositive r)).le
  rw [orderedAllPlusActionFlux_eq_pairwise]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (haction 1) (haction 2))
      (mul_nonneg (haction 0) (haction 2)))
    (mul_nonneg (haction 0) (haction 1))

/-- Every filtered ordered static summand is nonnegative. -/
theorem orderedPositiveAllPlusStaticTerm_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa : Real) (energy : OrderedModeIndex N → Real)
    (henergy : ∀ mode, 0 ≤ energy mode) (modes : OrderedModeTriple N) :
    0 ≤ orderedPositiveAllPlusStaticTerm m kappa energy modes := by
  unfold orderedPositiveAllPlusStaticTerm
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg kappa)
          (harmonicOrderedNormalizedInteractionWeight_nonneg m modes)))
      (orderedAllPlusActionFlux_nonneg m energy modes henergy hpositive)
  · simp [hpositive]

/-- Summing the ordered static term over every triple is exactly the physical
factor times the complete positive ordered all-plus flux. -/
theorem sum_orderedPositiveAllPlusStaticTerm_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa : Real) (energy : OrderedModeIndex N → Real) :
    (∑ modes : OrderedModeTriple N,
      orderedPositiveAllPlusStaticTerm m kappa energy modes) =
      4 * kappa ^ 2 * positiveOrderedAllPlusActionFluxSum m energy := by
  classical
  unfold orderedPositiveAllPlusStaticTerm
    positiveOrderedAllPlusActionFluxSum
    CouplingWeightedJacobianSpectralBudget.positiveCouplingWeightedTupleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp [hpositive]
    ring
  · simp [hpositive]

/-- The physical fixed-output all-distinct counterrotating static mass is a
subsum of the complete ordered all-plus mass. -/
theorem allDistinctCounterrotatingStaticFluxMass_le_orderedComplete
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (henergy : ∀ mode, 0 ≤ energy mode) :
    allDistinctCounterrotatingStaticFluxMass m kappa energy observed ≤
      4 * kappa ^ 2 *
        positiveOrderedAllPlusActionFluxSum m (orderedEnergy energy) := by
  classical
  let physicalTerm : QuadraticPhaseTerm N → Real :=
    physicalCounterrotatingStaticTerm m kappa energy observed
  let orderedTerm : OrderedModeTriple N → Real :=
    orderedPositiveAllPlusStaticTerm m kappa (orderedEnergy energy)
  have hsubset :=
    positiveAllDistinctCounterrotatingRepresentatives_subset_all m observed
  have hphysicalNonneg : ∀ q ∈ allCounterrotatingQuadraticPhaseTerms N,
      0 ≤ physicalTerm q := by
    intro q hq
    rw [allCounterrotatingQuadraticPhaseTerms, Finset.mem_image] at hq
    obtain ⟨inputModes, _hinput, rfl⟩ := hq
    exact physicalCounterrotatingStaticTerm_nonneg
      m kappa energy observed inputModes henergy
  have horderedNonneg : ∀ modes, 0 ≤ orderedTerm modes := by
    intro modes
    exact orderedPositiveAllPlusStaticTerm_nonneg
      m kappa (orderedEnergy energy)
      (fun k ↦ henergy (orderedIndexEquiv k)) modes
  calc
    allDistinctCounterrotatingStaticFluxMass m kappa energy observed =
        ∑ q ∈ positiveAllDistinctCounterrotatingRepresentatives m observed,
          physicalTerm q := by
      rfl
    _ ≤ ∑ q ∈ allCounterrotatingQuadraticPhaseTerms N,
          physicalTerm q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun q hq _ ↦ hphysicalNonneg q hq)
    _ = ∑ inputModes : Fin 2 → Lattice.Site N,
          physicalTerm (counterrotatingQuadraticPhaseTerm inputModes) := by
      unfold allCounterrotatingQuadraticPhaseTerms
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      exact counterrotatingQuadraticPhaseTerm_injective hab
    _ = ∑ inputModes : Fin 2 → Lattice.Site N,
          orderedTerm (fixedOutputOrderedTriple observed inputModes) := by
      apply Finset.sum_congr rfl
      intro inputModes _hinput
      exact physicalCounterrotatingStaticTerm_eq_ordered
        m hsimple kappa energy observed inputModes
    _ = ∑ modes ∈ Finset.univ.image (fixedOutputOrderedTriple observed),
          orderedTerm modes := by
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      exact fixedOutputOrderedTriple_injective observed hab
    _ ≤ ∑ modes : OrderedModeTriple N, orderedTerm modes :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
        (fun modes _hmodes _ ↦ horderedNonneg modes)
    _ = 4 * kappa ^ 2 *
          positiveOrderedAllPlusActionFluxSum m (orderedEnergy energy) :=
      sum_orderedPositiveAllPlusStaticTerm_eq m kappa (orderedEnergy energy)

/-- Explicit per-volume `O(N)` bound for the physical fixed-output
all-distinct counterrotating static mass. -/
theorem allDistinctCounterrotatingStaticFluxMass_div_volume_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (energyCeiling frequencyCeiling : Real)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyCeiling : ∀ mode, energy mode ≤ energyCeiling)
    (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling) :
    allDistinctCounterrotatingStaticFluxMass m kappa energy observed /
        (N : Real) ≤
      (3 / 2 : Real) * kappa ^ 2 * frequencyCeiling *
        energyCeiling ^ 2 := by
  have hNpos : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hsub := allDistinctCounterrotatingStaticFluxMass_le_orderedComplete
    m hsimple kappa energy observed henergy
  have hsubDiv := div_le_div_of_nonneg_right hsub hNpos.le
  exact hsubDiv.trans
    (four_kappa_sq_mul_positiveOrderedAllPlusActionFluxSum_div_volume_le
      m kappa (orderedEnergy energy) energyCeiling frequencyCeiling
      (fun k ↦ henergy (orderedIndexEquiv k))
      (fun k ↦ henergyCeiling (orderedIndexEquiv k))
      hfrequencyCeiling hfrequency)

/-- Undivided form of the same linear-volume estimate. -/
theorem allDistinctCounterrotatingStaticFluxMass_le_linear_volume
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (energyCeiling frequencyCeiling : Real)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyCeiling : ∀ mode, energy mode ≤ energyCeiling)
    (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling) :
    allDistinctCounterrotatingStaticFluxMass m kappa energy observed ≤
      ((3 / 2 : Real) * kappa ^ 2 * frequencyCeiling *
        energyCeiling ^ 2) * (N : Real) := by
  have hNpos : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  exact (div_le_iff₀ hNpos).1
    (allDistinctCounterrotatingStaticFluxMass_div_volume_le
      m hsimple kappa energy observed energyCeiling frequencyCeiling
      henergy henergyCeiling hfrequencyCeiling hfrequency)

end

end ArchonPhysics.FreeFPUTAllDistinctCounterrotatingStaticFluxVolumeBound
