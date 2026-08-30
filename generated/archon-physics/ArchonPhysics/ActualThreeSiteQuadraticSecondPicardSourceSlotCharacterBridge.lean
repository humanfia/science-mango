import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability

/-!
# Actual source-slot character bridge for the three-site ordinary family

This module connects the *actual* canonical `quadraticSecondPicard` history
source to the raw Physlib mismatch-character sum.  It then splits that full
finite sum into the literal four-element three-site ordinary outer-history
family and its complement.

The complement is retained explicitly: the four displayed histories are a
properly identified subfamily, not a replacement for the full second-Picard
source.  No kinetic equation, random-phase approximation, or asymptotic
closure is assumed here.
-/

namespace ArchonPhysics.ActualThreeSiteQuadraticSecondPicardSourceSlotCharacterBridge

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open MeasureTheory
open UnitAddTorus

noncomputable section

variable {N : Nat} [NeZero N]

/-- One literal raw mismatch-character contribution to the signed canonical
quadratic second-Picard source.  The phase/conjugate action is deliberately
applied to the entire orientation-corrected Physlib summand. -/
noncomputable def canonicalQuadraticSecondPicardRawCharacterTerm
    (a : Real) (entry : PhaseSign × OrderedModeIndex N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (st : CanonicalSample × Real) : Complex :=
  phaseSignActComplex entry.1
    ((orderedPhyslibOrientation
        (canonicalMass (N := N) st.1) entry.2 : Complex) *
      ((iteratedQuadraticSecondPicardStaticCoefficient
          (canonicalMass (N := N) st.1) 1
          (canonicalOrientedPhyslibFreeRadius (N := N) a st.1)
          (orderedPhyslibModeIndex entry.2) term *
        mFourier (iteratedQuadraticSecondPicardCharge term)
          (canonicalReindexedPhyslibHaarPhase (N := N) st.1)) *
        (Complex.exp
          ((Complex.I *
            (iteratedQuadraticOuterMismatch
              (canonicalMass (N := N) st.1)
              (orderedPhyslibModeIndex entry.2) term : Real)) * st.2) *
          oscillatoryIntegral
            (iteratedQuadraticInnerMismatch
              (canonicalMass (N := N) st.1) term) st.2)))

/-- On the simple-spectrum event, the actual canonical
`quadraticSecondPicard` source is exactly the full raw character sum. -/
theorem canonicalQuadraticSecondPicardHistorySource_eq_rawCharacterSum
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N) (time : Real) :
    canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .quadraticSecondPicard (omega, time) =
      ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        canonicalQuadraticSecondPicardRawCharacterTerm
          (N := N) a entry term (omega, time) := by
  rw [canonicalQuadraticSecondPicardSource_eq_measurableOrdered
    (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple entry time]
  unfold canonicalSignedQuadraticSecondPicardRotatedSource
  rw [canonicalOrderedQuadraticSecondPicardRotatedSource_eq_orientedPhyslib
    (N := N) 1 a omega hsimple entry.2 time]
  rw [physlibQuadraticSecondPicardRotatedSource_eq_mismatchSum]
  rcases entry with ⟨sign, observed⟩
  cases sign <;>
    simp [canonicalQuadraticSecondPicardRawCharacterTerm,
      phaseSignActComplex, Finset.mul_sum]

/-- One raw mismatch-character contribution after multiplication by the
unchanged factors in a displayed source slot. -/
noncomputable def canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
    {I : Type*} [DecidableEq I]
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (st : CanonicalSample × Real) : Complex :=
  (∏ j ∈ block.erase slot,
    canonicalSignedInteractionAmplitude (N := N)
      flowKappa flowBeta flowG hflowBeta a (entry j) st) *
    canonicalQuadraticSecondPicardRawCharacterTerm
      (N := N) a (entry slot) term st

/-- Exact pointwise transport of the raw character sum through an actual
source-slot multiplier. -/
theorem canonicalQuadraticSecondPicardHistorySourceSlot_eq_rawCharacterSum
    {I : Type*} [DecidableEq I]
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot .quadraticSecondPicard (omega, time) =
      ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
          (N := N) flowKappa flowBeta flowG hflowBeta a
          entry block slot term (omega, time) := by
  unfold canonicalQuadraticDuhamelHistorySourceSlotObservable
    canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
  rw [canonicalQuadraticSecondPicardHistorySource_eq_rawCharacterSum
    (N := N) flowKappa flowBeta flowG hflowBeta a omega hsimple
      (entry slot) time]
  rw [Finset.mul_sum]

/-! ## Literal N=3 four-term subfamily and complement -/

local instance :
    DecidableEq (IteratedQuadraticSecondPicardCharacterTerm 3) :=
  Classical.decEq _

/-- The literal image of the four ordinary three-site outer histories inside
the full raw second-Picard character index. -/
noncomputable def threeSiteOrdinaryOuterHistoryFinset :
    Finset (IteratedQuadraticSecondPicardCharacterTerm 3) :=
  Finset.univ.image threeSiteOrdinaryOuterHistoryTerm

@[simp] theorem mem_threeSiteOrdinaryOuterHistoryFinset
    (term : IteratedQuadraticSecondPicardCharacterTerm 3) :
    term ∈ threeSiteOrdinaryOuterHistoryFinset ↔
      ∃ index : ThreeSiteOrdinaryOuterHistoryIndex,
        threeSiteOrdinaryOuterHistoryTerm index = term := by
  classical
  simp [threeSiteOrdinaryOuterHistoryFinset]

/-- The selected literal image contains exactly four distinct raw terms. -/
@[simp] theorem card_threeSiteOrdinaryOuterHistoryFinset :
    threeSiteOrdinaryOuterHistoryFinset.card = 4 := by
  classical
  unfold threeSiteOrdinaryOuterHistoryFinset
  rw [Finset.card_image_of_injective _
    threeSiteOrdinaryOuterHistoryTerm_injective]
  simp

/-- Any full raw character sum splits exactly into the four-term ordinary
subfamily and the remaining raw histories. -/
theorem fullCharacterSum_eq_ordinaryOuter_add_complement
    (weight : IteratedQuadraticSecondPicardCharacterTerm 3 → Complex) :
    (∑ term, weight term) =
      (∑ term ∈ threeSiteOrdinaryOuterHistoryFinset, weight term) +
      (∑ term ∈
        Finset.univ \ threeSiteOrdinaryOuterHistoryFinset, weight term) := by
  classical
  simpa [add_comm] using
    (Finset.sum_sdiff (f := weight)
      (Finset.subset_univ threeSiteOrdinaryOuterHistoryFinset)).symm

/-- The actual three-site source slot is the literal four-term ordinary sum
plus the full complement, pointwise on the simple-spectrum event.

This algebraic decomposition permits any observed ordered mode.  Reusing the
existing N=3 outer-mismatch small-ball theorem additionally requires
`orderedPhyslibModeIndex (entry slot).2 = firstPositivePhysicalModeThree`;
no such probabilistic connection is asserted in this module. -/
theorem threeSiteQuadraticSecondPicardHistorySourceSlot_eq_ordinaryOuter_add_complement
    {I : Type*} [DecidableEq I]
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex 3)
    (block : Finset I) (slot : I)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := 3) omega)))
    (time : Real) :
    canonicalQuadraticDuhamelHistorySourceSlotObservable (N := 3)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := 3) a)
        (canonicalReindexedPhyslibHaarPhase (N := 3))
        entry block slot .quadraticSecondPicard (omega, time) =
      (∑ term ∈ threeSiteOrdinaryOuterHistoryFinset,
        canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
          (N := 3) flowKappa flowBeta flowG hflowBeta a
          entry block slot term (omega, time)) +
      (∑ term ∈ Finset.univ \ threeSiteOrdinaryOuterHistoryFinset,
        canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
          (N := 3) flowKappa flowBeta flowG hflowBeta a
          entry block slot term (omega, time)) := by
  rw [canonicalQuadraticSecondPicardHistorySourceSlot_eq_rawCharacterSum
    (N := 3) flowKappa flowBeta flowG hflowBeta a entry block slot omega
      hsimple time]
  exact fullCharacterSum_eq_ordinaryOuter_add_complement _

/-- Almost-sure version of the exact three-site source-slot split.  Spectrum
simplicity is discharged by the existing iid mass theorem. -/
theorem threeSiteQuadraticSecondPicardHistorySourceSlot_eq_ordinaryOuter_add_complement_ae
    {I : Type*} [DecidableEq I]
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex 3)
    (block : Finset I) (slot : I) (time : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := 3)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := 3) a)
          (canonicalReindexedPhyslibHaarPhase (N := 3))
          entry block slot .quadraticSecondPicard (omega, time) =
        (∑ term ∈ threeSiteOrdinaryOuterHistoryFinset,
          canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
            (N := 3) flowKappa flowBeta flowG hflowBeta a
            entry block slot term (omega, time)) +
        (∑ term ∈ Finset.univ \ threeSiteOrdinaryOuterHistoryFinset,
          canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
            (N := 3) flowKappa flowBeta flowG hflowBeta a
            entry block slot term (omega, time)) := by
  filter_upwards
    [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := 3)
      canonicalIIDMassPhaseEnsemble (by norm_num)] with omega hsimple
  apply
    threeSiteQuadraticSecondPicardHistorySourceSlot_eq_ordinaryOuter_add_complement
      flowKappa flowBeta flowG hflowBeta a entry block slot omega
  simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using hsimple

end
end ArchonPhysics.ActualThreeSiteQuadraticSecondPicardSourceSlotCharacterBridge
