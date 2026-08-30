import ArchonPhysics.FreeFPUTArbitraryGardenDenominatorCombinatorics
import ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall

/-!
# Arbitrary-garden compact-atlas small-denominator bridge

The denominator combinatorics for a fixed finite FPUT garden enumerates all
cumulative ordered-IBP denominators, not merely the local three-wave mismatch
at one vertex.  Already at order two the list contains `deltaOne + deltaTwo`.
Consequently there is no justified coercion from every garden coordinate to a
single `QuadraticPhaseTerm`/A1 mismatch chart.

This module introduces the exact scalar one-site-fiber interface needed for
one ordinary garden coordinate.  A certificate exposes its compact good set,
actual finite-atlas cardinality, positive Jacobian threshold, measurability,
and the restricted pushforward estimate delivered by a compact atlas.  The
existing actual A1 compact theorem constructs such a certificate when a
coordinate really is an A1 mismatch.  A genuinely cumulative higher-order
coordinate must receive its own certificate; no A1 identification is assumed.

For every ordinary coordinate in an arbitrary fixed-order garden, the finite
union bound is

`(sum_i atlasCoefficient_i) * ofReal (2 * gamma) + P(union_i K_iᶜ)`.

The compact bad union is charged once and no independence is used.  The
identically-zero, resonant-connected, and recollision sectors are retained
separately.  The final boundary theorem displays the two inputs which are
still absent from a kinetic closure: compact-atlas transversality for every
ordinary cumulative denominator and decay (or structural cancellation) of
the retained sector.  This is a frozen one-site mass-fiber statement, not an
annealed multi-site theorem, high-order RPA, re-Haar step, or Markov closure.
-/

namespace ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FreeFPUTArbitraryGardenDenominatorCombinatorics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set

noncomputable section

/-- The first genuinely higher-order ordered history contains a cumulative
sum denominator in addition to its two local phases.  Thus an A1 chart for a
local phase does not by itself certify the complete order-two list. -/
theorem orderedHistoryDenominators_two_eq_local_and_cumulative
    (deltaOne deltaTwo : Real) :
    orderedHistoryDenominators [deltaOne, deltaTwo] =
      [deltaOne, deltaTwo, deltaOne + deltaTwo] := by
  simp [orderedHistoryDenominators]

/-- Quantitative one-site compact-atlas endpoint for one scalar denominator
coordinate.  The `map_restrict_le` field is the actual transversality output;
it is not inferred from the coordinate being labelled ordinary. -/
structure OrdinaryGardenCoordinateCompactAtlas
    (coordinate : Real → Real) where
  compactSet : Set Real
  isCompact_compactSet : IsCompact compactSet
  atlasCard : Nat
  jacLower : Real
  jacLower_pos : 0 < jacLower
  coordinate_measurable : Measurable coordinate
  map_restrict_le : ∀ {target : Set Real}, MeasurableSet target →
    Measure.map coordinate (massCoordinateLaw.restrict compactSet) target ≤
      ((atlasCard : ENNReal) *
        ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹)) *
          (volume : Measure Real) target

/-- Regular density coefficient carried by one coordinate certificate. -/
def OrdinaryGardenCoordinateCompactAtlas.regularCoefficient
    {coordinate : Real → Real}
    (certificate : OrdinaryGardenCoordinateCompactAtlas coordinate) :
    ENNReal :=
  (certificate.atlasCard : ENNReal) *
    ((5 / 2 : ENNReal) *
      (ENNReal.ofReal certificate.jacLower)⁻¹)

/-- The existing actual A1 compact atlas supplies the coordinate interface
when the denominator really is one A1 mismatch.  This constructor is not
applied to general cumulative garden denominators. -/
theorem exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second)|) :
    ∃ certificate : OrdinaryGardenCoordinateCompactAtlas
        (fun second => physlibA1PairMismatchChart
          fixed site₁ site₂ observed term (first, second)),
      certificate.compactSet = K ∧ certificate.jacLower = j₀ := by
  obtain ⟨atlasCard, hregular, _hfull⟩ :=
    exists_atlasCard_physlibA1PairFiberCompact_smallBall
      fixed hsite observed term first K hK hKregular hj₀ hjac
  let chart : Real → Real := fun second =>
    physlibA1PairMismatchChart
      fixed site₁ site₂ observed term (first, second)
  have hchart : Measurable chart :=
    (measurable_physlibA1PairMismatchChart
      fixed site₁ site₂ observed term).comp
        (measurable_const.prodMk measurable_id)
  let certificate : OrdinaryGardenCoordinateCompactAtlas chart :=
    { compactSet := K
      isCompact_compactSet := hK
      atlasCard := atlasCard
      jacLower := j₀
      jacLower_pos := hj₀
      coordinate_measurable := hchart
      map_restrict_le := hregular }
  exact ⟨certificate, rfl, rfl⟩

/-- One certificate controls its centered near event inside its own compact
good set. -/
theorem measure_coordinateCompactAtlasGoodNear_le
    {coordinate : Real → Real}
    (certificate : OrdinaryGardenCoordinateCompactAtlas coordinate)
    (gamma : Real) :
    massCoordinateLaw
        (coordinate ⁻¹' Ioo (-gamma) gamma ∩ certificate.compactSet) ≤
      certificate.regularCoefficient * ENNReal.ofReal (2 * gamma) := by
  have heq :
      massCoordinateLaw
          (coordinate ⁻¹' Ioo (-gamma) gamma ∩ certificate.compactSet) =
        Measure.map coordinate
          (massCoordinateLaw.restrict certificate.compactSet)
            (Ioo (-gamma) gamma) := by
    rw [Measure.map_apply certificate.coordinate_measurable measurableSet_Ioo,
      Measure.restrict_apply
        (measurableSet_Ioo.preimage certificate.coordinate_measurable)]
  rw [heq]
  have hbound := certificate.map_restrict_le
    (target := Ioo (-gamma) gamma) measurableSet_Ioo
  rw [Real.volume_Ioo] at hbound
  convert hbound using 1 <;>
    simp [OrdinaryGardenCoordinateCompactAtlas.regularCoefficient]
  rw [show gamma + gamma = gamma * 2 by ring,
    ENNReal.ofReal_mul' (by norm_num : (0 : Real) ≤ 2)]
  norm_num [mul_assoc, mul_comm, mul_left_comm]

/-- Union of compact-atlas exceptional fibers over the ordinary garden
coordinates. -/
def ordinaryGardenCompactAtlasBadEvent
    (capacity : Nat) (coordinate : Fin capacity → Real → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex capacity sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i.1)) : Set Real :=
  ⋃ i, (certificate i).compactSetᶜ

/-- The good near event for one ordinary garden coordinate. -/
def ordinaryGardenCompactAtlasGoodNearEvent
    (capacity : Nat) (coordinate : Fin capacity → Real → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex capacity sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i.1))
    (i : GardenSectorIndex capacity sector .ordinaryNonresonant)
    (gamma : Real) : Set Real :=
  coordinate i.1 ⁻¹' Ioo (-gamma) gamma ∩
    (certificate i).compactSet

/-- Sum of the actual compact-atlas density coefficients of all ordinary
coordinates.  Its fixed-order dependence is intentionally visible. -/
def ordinaryGardenCompactAtlasRegularCoefficient
    (capacity : Nat) (coordinate : Fin capacity → Real → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex capacity sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i.1)) : ENNReal :=
  ∑ i, (certificate i).regularCoefficient

/-- Fixed finite garden union bound from per-coordinate scalar compact
atlases.  The bad compact union is charged once; no denominator-event
independence is used. -/
theorem measure_ordinaryGardenSmallEvent_le_compactAtlas
    (capacity : Nat) (coordinate : Fin capacity → Real → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex capacity sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i.1))
    (gamma : Real) :
    massCoordinateLaw
        (gardenSectorSmallDenominatorEvent capacity coordinate sector
          .ordinaryNonresonant gamma) ≤
      ordinaryGardenCompactAtlasRegularCoefficient
          capacity coordinate sector certificate *
            ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (ordinaryGardenCompactAtlasBadEvent
            capacity coordinate sector certificate) := by
  classical
  let bad := ordinaryGardenCompactAtlasBadEvent
    capacity coordinate sector certificate
  let goodNear : GardenSectorIndex capacity sector .ordinaryNonresonant →
      Set Real := fun i => ordinaryGardenCompactAtlasGoodNearEvent
        capacity coordinate sector certificate i gamma
  have hsubset :
      gardenSectorSmallDenominatorEvent capacity coordinate sector
          .ordinaryNonresonant gamma ⊆
        bad ∪ ⋃ i, goodNear i := by
    intro second hsecond
    rw [mem_gardenSectorSmallDenominatorEvent_iff] at hsecond
    rcases hsecond with ⟨index, hsector, hsmall⟩
    let i : GardenSectorIndex capacity sector .ordinaryNonresonant :=
      ⟨index, hsector⟩
    by_cases hbad : second ∈ bad
    · exact Or.inl hbad
    · apply Or.inr
      rw [mem_iUnion]
      refine ⟨i, (abs_lt.mp hsmall), ?_⟩
      by_contra hnotK
      exact hbad (mem_iUnion.mpr ⟨i, hnotK⟩)
  have hgoodBound : ∀ i,
      massCoordinateLaw (goodNear i) ≤
        (certificate i).regularCoefficient *
          ENNReal.ofReal (2 * gamma) := by
    intro i
    exact measure_coordinateCompactAtlasGoodNear_le
      (certificate i) gamma
  calc
    massCoordinateLaw
        (gardenSectorSmallDenominatorEvent capacity coordinate sector
          .ordinaryNonresonant gamma) ≤
      massCoordinateLaw (bad ∪ ⋃ i, goodNear i) := measure_mono hsubset
    _ ≤ massCoordinateLaw bad +
        massCoordinateLaw (⋃ i, goodNear i) := measure_union_le _ _
    _ ≤ massCoordinateLaw bad +
        ∑' i, massCoordinateLaw (goodNear i) := by
      gcongr
      exact measure_iUnion_le _
    _ ≤ massCoordinateLaw bad +
        ∑ i, (certificate i).regularCoefficient *
          ENNReal.ofReal (2 * gamma) := by
      simp only [tsum_fintype]
      gcongr with i
      exact hgoodBound i
    _ = ordinaryGardenCompactAtlasRegularCoefficient
          capacity coordinate sector certificate *
            ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw bad := by
      unfold ordinaryGardenCompactAtlasRegularCoefficient
      rw [Finset.sum_mul]
      ac_rfl

/-- The three sectors excluded from the ordinary compact-atlas estimate.
Identically-zero coordinates remain here unless a separate zero-interaction
coefficient theorem deletes them. -/
def gardenRetainedSmallDenominatorEvent
    (capacity : Nat) (coordinate : Fin capacity → Real → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (gamma : Real) : Set Real :=
  gardenSectorSmallDenominatorEvent capacity coordinate sector
      .identicallyZero gamma ∪
    gardenSectorSmallDenominatorEvent capacity coordinate sector
      .resonantConnected gamma ∪
    gardenSectorSmallDenominatorEvent capacity coordinate sector
      .recollision gamma

/-- Exact ordinary/retained partition of the complete padded garden small
event. -/
theorem finiteSmallDenominatorEvent_eq_ordinary_union_retained
    (capacity : Nat) (coordinate : Fin capacity → Real → Real)
    (sector : Fin capacity → GardenDenominatorSector) (gamma : Real) :
    finiteSmallDenominatorEvent coordinate gamma =
      gardenSectorSmallDenominatorEvent capacity coordinate sector
          .ordinaryNonresonant gamma ∪
        gardenRetainedSmallDenominatorEvent
          capacity coordinate sector gamma := by
  simpa [gardenRetainedSmallDenominatorEvent, union_assoc] using
    finiteSmallDenominatorEvent_eq_sector_union
      capacity coordinate sector gamma

/-- Arbitrary fixed-shape garden specialization.  Its capacity is the exact
combinatorial finite-union budget supplied by the garden module. -/
theorem measure_randomBranchingGardenOrdinarySmallEvent_le_compactAtlas
    (trees : List BinaryInteractionTree)
    (assignment : Real → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex
        (branchingGardenDenominatorCapacity trees) sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas
        (randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue i.1)) :
    massCoordinateLaw
        (gardenSectorSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector .ordinaryNonresonant gamma) ≤
      ordinaryGardenCompactAtlasRegularCoefficient
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (ordinaryGardenCompactAtlasBadEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector certificate) := by
  exact measure_ordinaryGardenSmallEvent_le_compactAtlas
    (branchingGardenDenominatorCapacity trees)
    (randomBranchingGardenDenominatorCoordinate
      trees assignment defaultValue)
    sector certificate gamma

/-- Exact arbitrary-garden decomposition into the controlled ordinary sector
and the explicitly retained identically-zero/resonant/recollision sector. -/
theorem randomBranchingGardenSmallEvent_eq_ordinary_union_retained
    (trees : List BinaryInteractionTree)
    (assignment : Real → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real) (hdefault : gamma ≤ |defaultValue|)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector) :
    {second | ∃ delta ∈
        branchingGardenDenominators trees (assignment second),
          |delta| < gamma} =
      gardenSectorSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector .ordinaryNonresonant gamma ∪
        gardenRetainedSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector gamma := by
  simpa [gardenRetainedSmallDenominatorEvent, union_assoc] using
    randomBranchingGardenSmallEvent_eq_sector_union
      trees assignment defaultValue gamma hdefault sector

/-- Full small-denominator bound with the retained sector left as its actual
mass.  This is the strongest unconditional conclusion of the bridge. -/
theorem measure_randomBranchingGardenSmallEvent_le_compactAtlas_add_retained
    (trees : List BinaryInteractionTree)
    (assignment : Real → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real) (hdefault : gamma ≤ |defaultValue|)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex
        (branchingGardenDenominatorCapacity trees) sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas
        (randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue i.1)) :
    massCoordinateLaw
        {second | ∃ delta ∈
          branchingGardenDenominators trees (assignment second),
            |delta| < gamma} ≤
      ordinaryGardenCompactAtlasRegularCoefficient
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (ordinaryGardenCompactAtlasBadEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector certificate) +
        massCoordinateLaw
          (gardenRetainedSmallDenominatorEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector gamma) := by
  rw [randomBranchingGardenSmallEvent_eq_ordinary_union_retained
    trees assignment defaultValue gamma hdefault sector]
  calc
    massCoordinateLaw
        (gardenSectorSmallDenominatorEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector .ordinaryNonresonant gamma ∪
          gardenRetainedSmallDenominatorEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector gamma) ≤
      massCoordinateLaw
          (gardenSectorSmallDenominatorEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector .ordinaryNonresonant gamma) +
        massCoordinateLaw
          (gardenRetainedSmallDenominatorEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector gamma) := measure_union_le _ _
    _ ≤ (ordinaryGardenCompactAtlasRegularCoefficient
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (ordinaryGardenCompactAtlasBadEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector certificate)) +
        massCoordinateLaw
          (gardenRetainedSmallDenominatorEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector gamma) := by
      gcongr
      exact measure_randomBranchingGardenOrdinarySmallEvent_le_compactAtlas
        trees assignment defaultValue gamma sector certificate

/-- Transparent closure boundary.  The `certificate` family is precisely the
still-missing higher-order transversality input for all ordinary cumulative
denominators.  The displayed `hretained` premise is the separate missing
resonant-connected/recollision decay (or structural cancellation) input.
Neither premise is obtained from pairwise A1 random-phase cancellation. -/
theorem measure_randomBranchingGardenSmallEvent_le_of_compactAtlas_of_retained
    (trees : List BinaryInteractionTree)
    (assignment : Real → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real) (hdefault : gamma ≤ |defaultValue|)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex
        (branchingGardenDenominatorCapacity trees) sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas
        (randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue i.1))
    (retainedBudget : ENNReal)
    (hretained : massCoordinateLaw
      (gardenRetainedSmallDenominatorEvent
        (branchingGardenDenominatorCapacity trees)
        (randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue)
        sector gamma) ≤ retainedBudget) :
    massCoordinateLaw
        {second | ∃ delta ∈
          branchingGardenDenominators trees (assignment second),
            |delta| < gamma} ≤
      ordinaryGardenCompactAtlasRegularCoefficient
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (ordinaryGardenCompactAtlasBadEvent
            (branchingGardenDenominatorCapacity trees)
            (randomBranchingGardenDenominatorCoordinate
              trees assignment defaultValue)
            sector certificate) + retainedBudget := by
  exact (measure_randomBranchingGardenSmallEvent_le_compactAtlas_add_retained
    trees assignment defaultValue gamma hdefault sector certificate).trans
      (add_le_add_right hretained _)

end

end ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
