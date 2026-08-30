import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
import ArchonPhysics.StrictDerivativeLocalLinearSmallBall

/-!
# Local linear small balls for an actual iterated-A2 mass fiber

The actual spectral module proves a strict scalar derivative for every
regular iterated-`A2` mismatch fiber.  Here a nonzero genuine vertical
Jacobian is converted directly into an open physical mass patch on which the
fiber is quantitatively antilipschitz.  Consequently both Lebesgue measure
and the uniform one-mass law obey an explicit linear centered-window bound.

Only strict differentiability at the base point is used: there is no added
`C²` or continuous-`fderiv` assumption.  This remains local.  A global
regular atlas, an actual bad-Jacobian estimate, and channel summability stay
as explicit later obligations.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2PairFiberLocalLinearSmallBall

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.StrictDerivativeLocalLinearSmallBall
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The actual second-mass mismatch fiber, named once for compact local
certificates. -/
def physlibIteratedA2PairMismatchFiber
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first second : Real) : Real :=
  physlibIteratedA2PairMismatchChart
    fixed site₁ site₂ channel observed term (first, second)

/-- The finite strict-inverse constant at a noncritical actual `A2` fiber
point.  Its definition keeps half of the derivative scale as nonlinear
error margin. -/
def physlibIteratedA2PairFiberAntilipschitzConstant
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (pair : Real × Real)
    (hjac : physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term pair ≠ 0) : NNReal :=
  strictDerivativeAntilipschitzConstant
    (physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term pair) hjac

/-- The uniform one-mass law inherits an antilipschitz centered-window bound
with its exact density ceiling `5/2`. -/
theorem massCoordinateLaw_inter_preimage_Icc_le_of_antilipschitz
    {chart : Real → Real} {patch : Set Real} {K : NNReal}
    (hanti : AntilipschitzWith K (patch.domRestrict chart))
    (center delta : Real) (hdelta : 0 ≤ delta) :
    massCoordinateLaw
        (patch ∩ chart ⁻¹' Icc (center - delta) (center + delta)) ≤
      (5 / 2 : ENNReal) *
        ((K : ENNReal) * ENNReal.ofReal (2 * delta)) := by
  let event := patch ∩ chart ⁻¹' Icc (center - delta) (center + delta)
  have hvolume : (volume : Measure Real) event ≤
      (K : ENNReal) * ENNReal.ofReal (2 * delta) :=
    volume_inter_preimage_Icc_le_of_antilipschitz
      hanti center delta hdelta
  calc
    massCoordinateLaw event ≤
        ((5 / 2 : ENNReal) • (volume : Measure Real)) event :=
      massCoordinateLaw_le_fiveHalves_smul_volume event
    _ = (5 / 2 : ENNReal) * (volume : Measure Real) event := by simp
    _ = (volume : Measure Real) event * (5 / 2 : ENNReal) := mul_comm _ _
    _ ≤ ((K : ENNReal) * ENNReal.ofReal (2 * delta)) *
        (5 / 2 : ENNReal) := mul_left_mono hvolume
    _ = (5 / 2 : ENNReal) *
        ((K : ENNReal) * ENNReal.ofReal (2 * delta)) := mul_comm _ _

/-- At an actual regular pair with nonzero vertical Jacobian, the second-mass
fiber admits an open measurable patch inside `massSupport`.  With the
displayed finite constant `K`, Lebesgue small balls cost at most `K * 2δ`
and the uniform mass law costs at most `(5/2) * K * 2δ`. -/
theorem exists_physlibIteratedA2PairFiber_localLinearSmallBall
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
  let fiber := physlibIteratedA2PairMismatchFiber
    fixed site₁ site₂ channel observed term pair.1
  let derivative := physlibIteratedA2PairMismatchVerticalJacobian
    fixed site₁ site₂ channel observed term pair
  have hstrict : HasStrictDerivAt fiber derivative pair.2 := by
    change HasStrictDerivAt
      (fun second => physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term (pair.1, second))
      (physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term pair) pair.2
    exact hasStrictDerivAt_physlibIteratedA2PairMismatchFiber
      fixed hsite channel observed term hregular
  have hpairInterior := hregular.1
  rw [iidMassPairSupport, interior_prod_eq] at hpairInterior
  have hmassNeighborhood : interior massSupport ∈ nhds pair.2 :=
    isOpen_interior.mem_nhds hpairInterior.2
  obtain ⟨patch, hopen, hmeasurable, hpoint, hsubsetInterior, hanti,
      hvolume⟩ :=
    exists_open_local_linearSmallBall_of_hasStrictDerivAt
      hstrict hjac hmassNeighborhood
  refine ⟨patch, ?_⟩
  dsimp only
  refine ⟨hopen, hmeasurable, hpoint,
    fun second hsecond ↦ interior_subset (hsubsetInterior hsecond), ?_, ?_⟩
  · simpa [fiber, derivative,
      physlibIteratedA2PairFiberAntilipschitzConstant] using hanti
  · intro center delta hdelta
    have hvolumePhysical := hvolume center delta hdelta
    have hmassPhysical :=
      massCoordinateLaw_inter_preimage_Icc_le_of_antilipschitz
        hanti center delta hdelta
    simpa [fiber, derivative,
      physlibIteratedA2PairFiberAntilipschitzConstant] using
        And.intro hvolumePhysical hmassPhysical

end

end ArchonPhysics.PhyslibFPUTIteratedA2PairFiberLocalLinearSmallBall
