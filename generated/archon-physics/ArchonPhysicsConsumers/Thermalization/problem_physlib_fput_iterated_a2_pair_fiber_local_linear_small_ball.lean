import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberLocalLinearSmallBall

/-!
# Consumer: actual iterated-A2 local linear small balls

This consumer checks the quantitative upgrade from a genuine nonzero actual
vertical Jacobian to a local `O(δ)` mismatch window.  The certificate uses
only the strict derivative already derived from the physical spectrum.  Its
Lebesgue coefficient is the explicit strict-inverse constant `K`; the
uniform one-mass law adds exactly the density ceiling `5/2`.

The result is intentionally local.  Actual bad-set control, an atlas cover,
and summability across the growing channel family remain visible research
obligations.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberLocalLinearSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.StrictDerivativeLocalLinearSmallBall
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- Consumer form of the actual local Lebesgue and uniform-mass linear
small-ball certificate. -/
theorem consumer_iteratedA2_regularNoncritical_has_localLinearSmallBall
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term)
    (hjac : physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term pair ≠ 0) :
    ∃ patch : Set Real,
      let fiber := physlibIteratedA2PairMismatchFiber
        fixed site₁ site₂ channel observed term pair.1
      let K := physlibIteratedA2PairFiberAntilipschitzConstant
        fixed site₁ site₂ channel observed term pair hjac
      IsOpen patch ∧ MeasurableSet patch ∧ pair.2 ∈ patch ∧
      patch ⊆ massSupport ∧
      AntilipschitzWith K (patch.domRestrict fiber) ∧
      ∀ center delta : Real, 0 ≤ delta →
        (volume : Measure Real)
            (patch ∩ fiber ⁻¹' Icc (center - delta) (center + delta)) ≤
              (K : ENNReal) * ENNReal.ofReal (2 * delta) ∧
        massCoordinateLaw
            (patch ∩ fiber ⁻¹' Icc (center - delta) (center + delta)) ≤
          (5 / 2 : ENNReal) *
            ((K : ENNReal) * ENNReal.ofReal (2 * delta)) := by
  exact exists_physlibIteratedA2PairFiber_localLinearSmallBall
    fixed hsite channel observed term hregular hjac

#print axioms
  exists_open_local_linearSmallBall_of_hasStrictDerivAt
#print axioms exists_physlibIteratedA2PairFiber_localLinearSmallBall
#print axioms
  consumer_iteratedA2_regularNoncritical_has_localLinearSmallBall

end

end ArchonPhysicsConsumers.Thermalization
