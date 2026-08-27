import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity

/-!
# Consumer: global all-distinct connected-return reconstruction

The local eight-tree images are globally complete after restricting the
quadratic terms to one canonical representative per input-swap orbit.  The
result below includes the positive-inner restriction used in the physical
feedback sum.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification

noncomputable section

/-- Existence of a canonical representative and local binary triple for an
arbitrary all-distinct connected matched tree. -/
theorem problem_exists_canonicalRepresentative_index
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hDistinct : ConnectedReturnTreeAllDistinct observed term.1)
    (hConnected : MatchedIteratedQuadraticConnectedChannel observed term.1) :
    ∃ q : QuadraticPhaseTerm N,
      q ∈ quadraticSwapOrbitRepresentatives N ∧
      ObservedQuadraticAllDistinct observed q ∧
      ∃ index : AllDistinctConnectedReturnIndex,
        allDistinctConnectedReturnMap observed q index = term :=
  exists_canonicalRepresentative_index_eq_of_allDistinct_connected
    observed term hDistinct hConnected

/-- The canonical representative and its three binary choices are jointly
unique. -/
theorem problem_canonicalRepresentative_localIndex_unique
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (qLeft qRight : QuadraticPhaseTerm N)
    (hLeftRep : qLeft ∈ quadraticSwapOrbitRepresentatives N)
    (hRightRep : qRight ∈ quadraticSwapOrbitRepresentatives N)
    (hLeftDistinct : ObservedQuadraticAllDistinct observed qLeft)
    (left right : AllDistinctConnectedReturnIndex)
    (heq : allDistinctConnectedReturnMap observed qLeft left =
      allDistinctConnectedReturnMap observed qRight right) :
    qLeft = qRight ∧ left = right :=
  canonicalRepresentative_localIndex_unique observed qLeft qRight
    hLeftRep hRightRep hLeftDistinct left right heq

/-- Global bijectivity before imposing inner-frequency positivity. -/
theorem problem_canonicalAllDistinctConnectedReturnMap_bijective
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    Function.Bijective
      (canonicalAllDistinctConnectedReturnMap observed) :=
  ⟨canonicalAllDistinctConnectedReturnMap_injective observed,
    canonicalAllDistinctConnectedReturnMap_surjective observed⟩

/-- Exact bijectivity on the positive-inner sector used by the compact
feedback sum. -/
theorem problem_positiveCanonicalAllDistinctConnectedReturnMap_bijective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Function.Bijective
      (positiveCanonicalAllDistinctConnectedReturnMap m observed) :=
  ⟨positiveCanonicalAllDistinctConnectedReturnMap_injective m observed,
    positiveCanonicalAllDistinctConnectedReturnMap_surjective m observed⟩

/-- The positive-sector inverse is a genuine right inverse. -/
theorem problem_positiveCanonicalMap_inverse
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : PositiveAllDistinctConnectedMatchedReturnTerm N m observed) :
    positiveCanonicalAllDistinctConnectedReturnMap m observed
        (positiveCanonicalAllDistinctConnectedReturnInverse
          m observed term) = term :=
  positiveCanonicalMap_inverse m observed term

#print axioms problem_exists_canonicalRepresentative_index
#print axioms problem_canonicalRepresentative_localIndex_unique
#print axioms problem_canonicalAllDistinctConnectedReturnMap_bijective
#print axioms problem_positiveCanonicalAllDistinctConnectedReturnMap_bijective
#print axioms problem_positiveCanonicalMap_inverse

end

end ArchonPhysicsConsumers.Thermalization
