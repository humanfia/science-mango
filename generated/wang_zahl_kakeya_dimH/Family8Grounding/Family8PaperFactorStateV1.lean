import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Family8Grounding.Family8ParentwiseBadParentActualFactorListSuccessorV1
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentIntervalProducerV1

/-!
# Paper-faithful heterogeneous factor state

Each actual factor carries its own admissibility proof, genuine coherent
multiscale cover, and exact Definition 2.12 data.  The readiness list is an
indexed inductive object matching the literal factor list, rather than a
callback that may return unrelated data.  In particular, this module never
constructs an identity cover for a fresh factor.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8PaperFactorStateV1

open Family8Def212ConvexWolffAtEveryScaleV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section
namespace ActualFactorDatum

/-- The family projection with the factor's stored finite instances supplied
explicitly. -/
def actualFamily (A : ActualFactorDatum) :=
  @ActualTubeDatum.family A.radius A.index
    A.fintypeIndex A.decidableEqIndex A.datum

end ActualFactorDatum

/-- The explicit recursive readiness data for one literal actual factor.

The coherent cover and exact Definition 2.12 package are fields supplied for
this exact atom.  No synthetic or identity hierarchy is manufactured here.
-/
structure PaperFactorAtomReadiness (A : ActualFactorDatum) where
  admissible :
    @ActualTubeDatum.IsAdmissible A.radius A.index
      A.fintypeIndex A.decidableEqIndex A.datum
  coherentCover :
    @CoherentStickyMultiscaleCover A.radius A.index
      A.fintypeIndex A.decidableEqIndex
        (Family8PaperFactorStateV1.ActualFactorDatum.actualFamily A)
  def212Constant : NNReal
  exactDef212 :
    @ExactScaleDef212Inputs A.radius A.index
      A.fintypeIndex A.decidableEqIndex
        (Family8PaperFactorStateV1.ActualFactorDatum.actualFamily A)
        (@CoherentStickyMultiscaleCover.base A.radius A.index
          A.fintypeIndex A.decidableEqIndex
            (Family8PaperFactorStateV1.ActualFactorDatum.actualFamily A)
            coherentCover)
        def212Constant

/-- Readiness certificates aligned structurally with every actual factor in
one literal list.  This indexed list prevents readiness for one atom from
being silently reused for another atom. -/
inductive PaperFactorReadinessList : List ActualFactorDatum → Type 2
  | nil : PaperFactorReadinessList []
  | cons {A : ActualFactorDatum} {tail : List ActualFactorDatum} :
      PaperFactorAtomReadiness A →
      PaperFactorReadinessList tail →
      PaperFactorReadinessList (A :: tail)

namespace PaperFactorReadinessList

/-- Structural concatenation of per-atom readiness certificates. -/
def append {left right : List ActualFactorDatum} :
    PaperFactorReadinessList left →
    PaperFactorReadinessList right →
    PaperFactorReadinessList (left ++ right)
  | .nil, hright => hright
  | .cons head tail, hright => .cons head (append tail hright)

end PaperFactorReadinessList

/-- A paper factor state is a literal heterogeneous list of actual factors
and readiness data aligned with every atom of that same list. -/
structure PaperFactorState where
  factors : List ActualFactorDatum
  readiness : PaperFactorReadinessList factors

/-- Package a literal list and its structurally aligned readiness data. -/
def PaperFactorState.ofFactors
    (factors : List ActualFactorDatum)
    (readiness : PaperFactorReadinessList factors) :
    PaperFactorState where
  factors := factors
  readiness := readiness

@[simp] theorem PaperFactorState.ofFactors_factors
    (factors : List ActualFactorDatum)
    (readiness : PaperFactorReadinessList factors) :
    (PaperFactorState.ofFactors factors readiness).factors = factors :=
  rfl

#print axioms PaperFactorAtomReadiness
#print axioms PaperFactorReadinessList.append
#print axioms PaperFactorState
#print axioms PaperFactorState.ofFactors

end
end Family8PaperFactorStateV1
