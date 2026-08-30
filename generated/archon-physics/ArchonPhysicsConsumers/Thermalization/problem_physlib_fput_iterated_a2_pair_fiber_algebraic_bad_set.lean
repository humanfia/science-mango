import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

/-- Consumer-facing form: finite algebraic certificates delete every genuine
regularity failure for a nonacoustic actual A2 channel at fixed volume. -/
example {N : Nat} [NeZero N] {fixed : Lattice.PositiveMassConfig N}
    {site₁ site₂ : Lattice.Site N} {channel : IteratedA2MismatchChannel}
    {observed : Lattice.Site N}
    {term : IteratedQuadraticSecondPicardCharacterTerm N}
    (certificate : IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term)
    (havoid : IteratedA2ChannelAvoidsAcoustic channel observed term) :
    iidMassPairLaw certificate.regularSetᶜ = 0 := by
  exact certificate.badSet_eq_zero havoid

/-- Consumer-facing structural warning: a participating acoustic mode makes
the positive-frequency differentiability source fail everywhere. -/
example {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hacoustic :
      orderedIndexEquiv (lastOrderedIndex (ι := Lattice.Site N)) ∈
        iteratedA2ChannelParticipatingModes channel observed term)
    (pair : Real × Real) :
    pair ∉ physlibIteratedA2PairMismatchDifferentiabilitySource
      fixed site₁ site₂ channel observed term := by
  exact not_mem_differentiabilitySource_of_acoustic_participates
    fixed site₁ site₂ channel observed term hacoustic pair

#print axioms iidMassPair_mem_interior_ae
#print axioms iidMassPairLaw_twoSite_not_simple_eq_zero
#print axioms IteratedA2PairAlgebraicRegularityCertificate.badSet_eq_zero

end

end ArchonPhysicsConsumers.Thermalization
