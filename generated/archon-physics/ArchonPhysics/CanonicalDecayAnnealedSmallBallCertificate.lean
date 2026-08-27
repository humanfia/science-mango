import ArchonPhysics.CanonicalDecayAnnealedMainSectorSmallBallReduction

/-!
# Full canonical decay small-ball certificate from the two main sectors

Only the all-distinct and child-repeated annealed estimates remain as model
inputs.  The exact four-sector identity and the automatic quadratic bounds
for both parent--child sectors produce the full marked mismatch certificate.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalDecayAnnealedSmallBallCertificate

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalDecayAnnealedMainSectorSmallBallReduction
open ArchonPhysics.CanonicalDecayAnnealedParentChildSmallBall
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedSmallBallBridge
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- A sector estimate indexed by the marked-measure volume convention.  At
marked index `n`, the matching decay sector is indexed by `n + 1`. -/
structure CanonicalDecaySectorAnnealedMarkedIndexSmallBallBound
    (keep : {N : Nat} → [NeZero N] → OrderedModeTriple N → Prop) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  error : Nat → Real
  error_nonneg : ∀ n, 0 ≤ error n
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound : ∀ n : Nat, ∀ delta : Real,
    0 < delta → delta ≤ 1 →
    ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        keep (n + 1) : Measure Real)
        (absoluteMismatchSublevel delta)).toReal ≤
      constant * delta + error n

/-- The two unresolved main-sector estimates imply the full canonical
annealed marked mismatch estimate.  The added `5/4` is exactly the sum of the
two automatic `5/8 * delta^2` parent--child bounds, weakened linearly on
`0 < delta ≤ 1`. -/
def canonicalMarkedMismatchAnnealedSmallBallBound_of_decayMainSectors
    (allDistinct : CanonicalDecaySectorAnnealedMarkedIndexSmallBallBound
      (fun {_N} _inst ↦ AllDistinctModes))
    (childRepeated : CanonicalDecaySectorAnnealedMarkedIndexSmallBallBound
      (fun {_N} _inst ↦ ChildRepeated)) :
    CanonicalMarkedMismatchAnnealedVanishingErrorSmallBallBound
      decayInteractionSign where
  constant := allDistinct.constant + childRepeated.constant + 5 / 4
  constant_nonneg :=
    add_nonneg
      (add_nonneg allDistinct.constant_nonneg childRepeated.constant_nonneg)
      (by norm_num)
  error := fun n ↦ allDistinct.error n + childRepeated.error n
  error_nonneg := fun n ↦
    add_nonneg (allDistinct.error_nonneg n) (childRepeated.error_nonneg n)
  error_tendsto_zero := by
    simpa using
      allDistinct.error_tendsto_zero.add childRepeated.error_tendsto_zero
  bound := by
    intro n delta hdelta hdelta1
    have hall := allDistinct.bound n delta hdelta hdelta1
    have hchild := childRepeated.bound n delta hdelta hdelta1
    have hone := canonicalDecaySectorAnnealed_parentChildOne_smallBall
      (n + 1) hdelta hdelta1
    have htwo := canonicalDecaySectorAnnealed_parentChildTwo_smallBall
      (n + 1) hdelta hdelta1
    calc
      _ ≤
          ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
              (fun {_N} _inst ↦ AllDistinctModes) (n + 1) : Measure Real)
              (absoluteMismatchSublevel delta)).toReal +
            ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
              (fun {_N} _inst ↦ ChildRepeated) (n + 1) : Measure Real)
              (absoluteMismatchSublevel delta)).toReal +
            ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
              (fun {_N} _inst ↦ ParentChildOneRepeated) (n + 1) : Measure Real)
              (absoluteMismatchSublevel delta)).toReal +
            ((canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
              (fun {_N} _inst ↦ ParentChildTwoRepeated) (n + 1) : Measure Real)
              (absoluteMismatchSublevel delta)).toReal :=
        canonicalMarkedMismatchAnnealed_decay_apply_toReal_le_sectorSum
          n (absoluteMismatchSublevel delta)
      _ ≤
          (allDistinct.constant * delta + allDistinct.error n) +
            (childRepeated.constant * delta + childRepeated.error n) +
            (5 / 8 : Real) * delta ^ 2 +
            (5 / 8 : Real) * delta ^ 2 :=
        add_le_add (add_le_add (add_le_add hall hchild) hone) htwo
      _ ≤
          (allDistinct.constant + childRepeated.constant + 5 / 4) * delta +
            (allDistinct.error n + childRepeated.error n) := by
        have hquadratic : 0 ≤ delta * (1 - delta) :=
          mul_nonneg hdelta.le (sub_nonneg.mpr hdelta1)
        nlinarith

/-- Direct deterministic collision-limit endpoint after the two main-sector
annealed estimates have been discharged. -/
theorem canonicalCollisionPerSiteMeasureLimit_decay_singleton_zero_eq_zero
    (allDistinct : CanonicalDecaySectorAnnealedMarkedIndexSmallBallBound
      (fun {_N} _inst ↦ AllDistinctModes))
    (childRepeated : CanonicalDecaySectorAnnealedMarkedIndexSmallBallBound
      (fun {_N} _inst ↦ ChildRepeated)) :
    (canonicalCollisionPerSiteMeasureLimit canonicalIIDMassPhaseEnsemble
        decayInteractionSign : Measure Real) ({0} : Set Real) = 0 :=
  canonicalCollisionPerSiteMeasureLimit_singleton_zero_eq_zero_of_annealedSmallBall
    (canonicalMarkedMismatchAnnealedSmallBallBound_of_decayMainSectors
      allDistinct childRepeated)

end


end ArchonPhysics.CanonicalDecayAnnealedSmallBallCertificate
