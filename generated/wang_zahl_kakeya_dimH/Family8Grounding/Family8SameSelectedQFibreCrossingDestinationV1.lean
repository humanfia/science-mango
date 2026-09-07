import Family8Grounding.Family8PaperFactorFiniteRunV2
import Family8Grounding.Family8ParentwisePointwiseCrossingIntegratedSuccessorV1
import Family8Grounding.Family8SelectedFiberFaithfulCoherentSuccessorV1
import Mathlib.Tactic

/-!
# The literal q-fibre destination of one paper crossing step

This module fixes the object seam between a parentwise crossing successor and
the next selector.  The destination datum is definitionally the one selected
q-fibre child already stored by the integrated successor; its coherent cover
is definitionally the faithful q-fresh cover.  Consequently no destination
datum, parent, or selected subtype is repicked.

The positive source correlation records the exact same-q StateV2 base, the
same selected subtype, the raw strict crossing, the raw pointwise upper bound,
and membership of the literal fresh atom in the paper successor list.

This file deliberately does not manufacture the still-missing current-stage
lower bound.  To obtain it, the faithful hierarchy must additionally identify
every fibre of the destination raw interval cover with a fibre inside the
same selected source q-fibre, including an index equivalence and equality (or
quantitative two-sided comparison) of every family body and of the ambient
parent under the common contracted-John/eighth map.  Carrier inclusion alone
does not transport `canonicalFrostmanConstant` in the required lower
direction.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped ENNReal NNReal

namespace Family8SameSelectedQFibreCrossingDestinationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8ContractedJohnActualTubeProxyV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseBadParentPaperFactorTransitionV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8ParentwisePointwiseCrossingIntegratedSuccessorV1
open Family8SelectedFiberFaithfulCoherentSuccessorV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}
  {Wsrc : FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N}

/-- The fresh q-fibre atom is a literal member of the paper successor list.
This follows from the list definition; it is not an external successor-atom
witness. -/
theorem qFibreChildAtom_mem_paperSuccessor
    (step : SameObjectCrossingPaperStep Wsrc) :
    step.integrated.dualChild.qFibreChildAtom ∈
      step.paperTransition.successor.factors := by
  rw [step.paperTransition.successor_factors_eq]
  simp only [
    ParentwiseBadParentMassAwareFactorListState.successorFactors,
    badParentSuccessorFactorList, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (Or.inl rfl))

/-- All source facts needed by the next analytic transport, pinned to one
integrated successor and one paper transition.  In particular, the upper and
strict inequalities remain in their honest directions. -/
structure SameSelectedQFibreSourceCorrelation
    (step : SameObjectCrossingPaperStep Wsrc) : Prop where
  same_qFibre_base :
    step.integrated.integrated.factorState =
      step.integrated.dualChild.qFibreState.base
  same_selected :
    step.integrated.integrated.factorState.selected =
      step.integrated.dualChild.qFibreState.base.selected
  raw_interval_strict :
    parentNormalizedFiberCFAt
        (paperBufferedIntervalCover
          D hD C S epsilon hepsilon Wsrc.m Wsrc.rho Wsrc.buffered)
        Wsrc.q < crossingStopLower Wsrc
  raw_interval_upper :
    parentNormalizedFiberCFAt
        (paperBufferedIntervalCover
          D hD C S epsilon hepsilon Wsrc.m Wsrc.rho Wsrc.buffered)
        Wsrc.q <=
      step.integrated.readiness.baseError *
        step.integrated.readiness.massUpper *
          step.integrated.readiness.massLower⁻¹
  fresh_atom_mem :
    step.integrated.dualChild.qFibreChildAtom ∈
      step.paperTransition.successor.factors

/-- Callback-free producer of the complete same-selected source correlation.
Every field is a theorem of the single integrated successor stored in
`step`. -/
theorem sameSelectedQFibreSourceCorrelation
    (step : SameObjectCrossingPaperStep Wsrc) :
    SameSelectedQFibreSourceCorrelation step where
  same_qFibre_base := step.same_qFibre_base
  same_selected :=
    step.integrated.integrated_selected_eq_qFibreSelected
  raw_interval_strict := step.integrated.raw_interval_strict
  raw_interval_upper := rawIntervalUpper step.integrated
  fresh_atom_mem := qFibreChildAtom_mem_paperSuccessor step

/-- The next crossing on the q-fibre branch, tied definitionally to the
actual fresh datum and faithful coherent cover of the source step.

The only remaining input here is a genuine selector witness on that exact
object.  There is no heterogeneous datum equality and no list-membership
assumption to discharge later. -/
structure SameSelectedQFibreCrossingDestination
    (step : SameObjectCrossingPaperStep Wsrc) where
  faithful :
    SelectedFiberFaithfulCoherentSuccessor Wsrc step.integrated
  destinationDepth : Nat
  destinationScales : FiniteScaleSequence
    (badParentFreshChildRadius delta Wsrc.rho) destinationDepth
  destinationEpsilon : Real
  destinationEpsilon_nonneg : 0 <= destinationEpsilon
  destinationEta : Nat -> Real
  destination : FirstParentwiseNormalizedCrossingWitness
    step.integrated.dualChild.qFibreChildDatum
    step.integrated.dualChild.qFibreChild_admissible
    faithful.readiness.qFreshCover destinationScales
    destinationEpsilon destinationEpsilon_nonneg destinationEta N

namespace SameSelectedQFibreCrossingDestination

variable {step : SameObjectCrossingPaperStep Wsrc}

/-- The heterogeneous destination atom is definitionally the literal q-fibre
child atom already stored by the integrated successor. -/
@[simp] theorem destinationAtom_eq_qFibreChildAtom
    (_Y : SameSelectedQFibreCrossingDestination step) :
    ActualFactorDatum.ofDatum step.integrated.dualChild.qFibreChildDatum =
      step.integrated.dualChild.qFibreChildAtom :=
  rfl

/-- Therefore the exact datum on which the destination selector runs is a
member of the exact paper successor state. -/
theorem destinationAtom_mem_paperSuccessor
    (_Y : SameSelectedQFibreCrossingDestination step) :
    ActualFactorDatum.ofDatum step.integrated.dualChild.qFibreChildDatum ∈
      step.paperTransition.successor.factors := by
  simpa only [destinationAtom_eq_qFibreChildAtom] using
    qFibreChildAtom_mem_paperSuccessor step

/-- Re-export the source correlation from the exact destination object. -/
theorem sourceCorrelation
    (_Y : SameSelectedQFibreCrossingDestination step) :
    SameSelectedQFibreSourceCorrelation step :=
  sameSelectedQFibreSourceCorrelation step

end SameSelectedQFibreCrossingDestination

#print axioms qFibreChildAtom_mem_paperSuccessor
#print axioms SameSelectedQFibreSourceCorrelation
#print axioms sameSelectedQFibreSourceCorrelation
#print axioms SameSelectedQFibreCrossingDestination
#print axioms
  SameSelectedQFibreCrossingDestination.destinationAtom_mem_paperSuccessor

end
end Family8SameSelectedQFibreCrossingDestinationV1
