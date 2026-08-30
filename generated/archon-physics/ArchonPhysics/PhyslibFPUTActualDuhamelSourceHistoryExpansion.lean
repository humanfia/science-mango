import ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
import ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

/-!
# Actual finite-ensemble Duhamel sources through second Picard order

For each finite-ensemble member, the actual unit quadratic source is exactly
the sum of its free first-Picard source, extracted quadratic second-Picard
source, linear history remainder, and defect-square source.  The actual unit
quartic source is exactly its free cubic second-Picard source plus the literal
actual-minus-free cubic remainder.  No RPA, gap, or limiting input is used.
-/

namespace ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion

open scoped BigOperators
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

noncomputable section

inductive ActualQuadraticSourceHistory where
  | freeFirstPicard
  | quadraticSecondPicard
  | linearHistoryRemainder
  | defectSquare
  deriving DecidableEq, Repr

inductive ActualQuarticSourceHistory where
  | freeCubicSecondPicard
  | cubicHistoryRemainder
  deriving DecidableEq, Repr

def actualQuadraticSourceHistories : Finset ActualQuadraticSourceHistory :=
  {.freeFirstPicard, .quadraticSecondPicard,
    .linearHistoryRemainder, .defectSquare}

def actualQuarticSourceHistories : Finset ActualQuarticSourceHistory :=
  {.freeCubicSecondPicard, .cubicHistoryRemainder}

/-- Conservative sector assignment: explicit Picard terms stay in the
unresolved small-denominator sector until a genuine gap split is proved. -/
def actualQuadraticHistorySector :
    ActualQuadraticSourceHistory -> GardenHistorySector
  | .freeFirstPicard => .badSmallDenominator
  | .quadraticSecondPicard => .badSmallDenominator
  | .linearHistoryRemainder => .truncationRemainder
  | .defectSquare => .recollisionRepeatedHistory

def actualQuarticHistorySector :
    ActualQuarticSourceHistory -> GardenHistorySector
  | .freeCubicSecondPicard => .badSmallDenominator
  | .cubicHistoryRemainder => .truncationRemainder

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

def actualFiniteQuadraticHistorySource
    {N : Nat} [NeZero N]
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (history : ActualQuadraticSourceHistory) :
    Omega -> I -> Real -> Complex :=
  fun omega i time => phaseSignActComplex (entry i).1 <|
    match history with
    | .freeFirstPicard =>
        physlibFreeQuadraticRotatedSource
          (mass omega) 1 1 (entry i).2 (radius omega) (phase omega) time
    | .quadraticSecondPicard =>
        physlibQuadraticSecondPicardRotatedSource
          (mass omega) 1 (entry i).2 (radius omega) (phase omega) time
    | .linearHistoryRemainder =>
        physlibQuadraticLinearHistoryRemainderRotatedSource
          (mass omega) 1 1 (entry i).2 (q omega)
            (radius omega) (phase omega) time
    | .defectSquare =>
        physlibQuadraticDefectSquareRotatedSource
          (mass omega) 1 1 (entry i).2 (q omega)
            (radius omega) (phase omega) time

def actualFiniteQuarticHistorySource
    {N : Nat} [NeZero N]
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N))
    (history : ActualQuarticSourceHistory) :
    Omega -> I -> Real -> Complex :=
  fun omega i time => phaseSignActComplex (entry i).1 <|
    match history with
    | .freeCubicSecondPicard =>
        physlibFreeCubicSecondPicardRotatedSource
          (mass omega) 1 (entry i).2 (radius omega) (phase omega) time
    | .cubicHistoryRemainder =>
        physlibCubicHistoryRemainderRotatedSource
          (mass omega) 1 1 (entry i).2 (q omega)
            (radius omega) (phase omega) time

/-- Exact samplewise four-history reconstruction of the actual signed unit
quadratic source. -/
theorem actualFiniteQuadraticUnitSource_eq_historySum
    {N : Nat} [NeZero N]
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N)) :
    actualFiniteCubicEnsembleSource mass 1 1 entry q =
      fun omega i time =>
        ∑ history ∈ actualQuadraticSourceHistories,
          actualFiniteQuadraticHistorySource mass entry q radius phase
            history omega i time := by
  funext omega i time
  have hraw :
      physlibQuadraticRotatedSource
          (mass omega) 1 1 (entry i).2 (q omega) time =
        physlibFreeQuadraticRotatedSource
            (mass omega) 1 1 (entry i).2
              (radius omega) (phase omega) time +
          physlibQuadraticSecondPicardRotatedSource
              (mass omega) 1 (entry i).2
                (radius omega) (phase omega) time +
          physlibQuadraticLinearHistoryRemainderRotatedSource
              (mass omega) 1 1 (entry i).2 (q omega)
                (radius omega) (phase omega) time +
          physlibQuadraticDefectSquareRotatedSource
              (mass omega) 1 1 (entry i).2 (q omega)
                (radius omega) (phase omega) time := by
    calc
      physlibQuadraticRotatedSource
          (mass omega) 1 1 (entry i).2 (q omega) time =
          physlibFreeQuadraticRotatedSource
              (mass omega) 1 1 (entry i).2
                (radius omega) (phase omega) time +
            physlibQuadraticHistoryDifference
              (mass omega) 1 1 (entry i).2 (q omega)
                (radius omega) (phase omega) time := by
            unfold physlibQuadraticHistoryDifference
            ring
      _ = physlibFreeQuadraticRotatedSource
              (mass omega) 1 1 (entry i).2
                (radius omega) (phase omega) time +
            (physlibQuadraticLinearHistoryRotatedSource
                (mass omega) 1 1 (entry i).2 (q omega)
                  (radius omega) (phase omega) time +
              physlibQuadraticDefectSquareRotatedSource
                (mass omega) 1 1 (entry i).2 (q omega)
                  (radius omega) (phase omega) time) := by
            rw [physlibQuadraticHistoryDifference_eq_linear_add_defectSquare]
      _ = _ := by
            rw [physlibQuadraticLinearHistoryRotatedSource_eq_secondPicard_add_remainder]
            norm_num
            ring
  unfold actualFiniteCubicEnsembleSource
    signedPhyslibCubicLeadingQuadraticSource
    physlibCubicLeadingQuadraticSource
  cases hsign : (entry i).1 with
  | phase =>
      simpa [actualQuadraticSourceHistories,
        actualFiniteQuadraticHistorySource, hsign,
        phaseSignActComplex, physlibQuadraticRotatedSource, add_assoc]
        using hraw
  | conjugate =>
      have hstar := congrArg star hraw
      simpa [actualQuadraticSourceHistories,
        actualFiniteQuadraticHistorySource, hsign,
        phaseSignActComplex, physlibQuadraticRotatedSource, add_assoc]
        using hstar

/-- Exact samplewise two-history reconstruction of the actual signed unit
quartic source. -/
theorem actualFiniteQuarticUnitSource_eq_historySum
    {N : Nat} [NeZero N]
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (q : Omega -> Time -> HilbertConfiguration N)
    (radius : Omega -> Lattice.Site N -> Real)
    (phase : Omega -> UnitAddTorus (Lattice.Site N)) :
    actualFiniteQuarticEnsembleSource mass 1 1 entry q =
      fun omega i time =>
        ∑ history ∈ actualQuarticSourceHistories,
          actualFiniteQuarticHistorySource mass entry q radius phase
            history omega i time := by
  funext omega i time
  have hraw :
      physlibCubicRotatedSource
          (mass omega) 1 1 (entry i).2 (q omega) time =
        physlibFreeCubicSecondPicardRotatedSource
            (mass omega) 1 (entry i).2
              (radius omega) (phase omega) time +
          physlibCubicHistoryRemainderRotatedSource
            (mass omega) 1 1 (entry i).2 (q omega)
              (radius omega) (phase omega) time := by
    simpa using
      (physlibCubicRotatedSource_eq_secondPicard_add_remainder
        (mass omega) 1 1 (entry i).2 (q omega)
          (radius omega) (phase omega) time)
  unfold actualFiniteQuarticEnsembleSource
    signedPhyslibQuarticForceRotatedSource
    physlibQuarticForceRotatedSource
  cases hsign : (entry i).1 with
  | phase =>
      simpa [actualQuarticSourceHistories,
        actualFiniteQuarticHistorySource, hsign,
        phaseSignActComplex, add_assoc] using hraw
  | conjugate =>
      have hstar := congrArg star hraw
      simpa [actualQuarticSourceHistories,
        actualFiniteQuarticHistorySource, hsign,
        phaseSignActComplex, add_assoc] using hstar

end
end ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
