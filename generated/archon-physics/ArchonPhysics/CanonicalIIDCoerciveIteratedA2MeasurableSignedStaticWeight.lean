import ArchonPhysics.CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability
import ArchonPhysics.RandomMassMeasurableOrderedEigenframe
import ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining

/-!
# A measurable signed-frame replacement for the iterated-A2 static weight

The legacy Physlib coefficient is built from Mathlib's noncomputable
`eigenvectorBasis`.  Its sign as the mass matrix varies has no measurable API,
and the complete iterated-A2 tree is not sign-invariant: after the repeated
inner mode cancels, the output, free, and two leaf orientations remain.

This file therefore constructs the honest replacement.  Every interaction
tensor is evaluated in the repository's globally measurable first-positive-
pivot eigenframe.  Measurable mass coordinates and measurable radius
coordinates then imply global measurability of the signed static weight.

On simple spectrum the signed coefficient is exactly the legacy coefficient
times an explicit product of two tensor-orientation signs.  In particular its
norm agrees with the legacy norm, but the complex coefficients themselves
are deliberately not claimed equal.  For iid continuous masses the relation
and norm equality hold almost surely, and the signed coefficient is
integrable under the same deterministic ceiling as the legacy coefficient.

No random-phase, Fourier-density, kinetic, or thermodynamic-limit statement
is made here.
-/

namespace ArchonPhysics
namespace CanonicalIIDCoerciveIteratedA2MeasurableSignedStaticWeight

open scoped Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableHarmonicData
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassOrderedProjectorBridge
open MeasureTheory

noncomputable section

/-! ## The globally measurable signed tensor and coefficient -/

/-- Bond coordinate of the first-positive-pivot signed ordered eigenvector,
reindexed by the legacy Physlib mode label. -/
def signedBondModeCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond mode : Lattice.Site N) : Real :=
  Matrix.mulVec (massWeightedDifferenceMatrix m)
    (signedOrderedEigenvector (harmonicHermitian m)
      ((orderedIndexEquiv (ι := Lattice.Site N)).symm mode)) bond

/-- Interaction tensor in the globally measurable signed frame. -/
def signedInteractionTensor {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat)
    (modes : Fin n -> Lattice.Site N) : Real :=
  ∑ bond, ∏ r, signedBondModeCoefficient m bond (modes r)

/-- Signed-frame version of one quadratic character coefficient. -/
def signedQuadraticPhaseCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N -> Real) (term : QuadraticPhaseTerm N) : Complex :=
  (signedInteractionTensor m 3 (Fin.cons observed term.1) : Complex) *
    ((radius (term.1 0) / 2 : Real) : Complex) *
    ((radius (term.1 1) / 2 : Real) : Complex)

/-- Signed-frame version of the deterministic free quadratic Duhamel
coefficient. -/
def signedFreeQuadraticDuhamelCoefficient {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N -> Real)
    (term : QuadraticPhaseTerm N) : Complex :=
  coupling * signedQuadraticPhaseCoefficient m observed radius term

/-- Signed-frame version of one first-Picard coordinate branch. -/
def signedFirstPicardCoordinateBranchStaticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) : Complex :=
  if 0 < modeFrequency m innerObserved then
    (((physlibQuadraticFirstPicardCoordinateScale m innerObserved / 2 : Real) :
        Complex) *
      if entry.2 = 0 then
        signedFreeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 innerObserved)
          m innerObserved radius entry.1
      else
        starRingEnd Complex
          (signedFreeQuadraticDuhamelCoefficient
            (physlibQuadraticCoupling m kappa 1 innerObserved)
            m innerObserved radius entry.1))
  else 0

/-- One complete iterated-A2 tree evaluated in the globally measurable
signed eigenframe. -/
def signedIteratedQuadraticSecondPicardStaticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  if 0 < modeFrequency m observed then
    physlibIteratedQuadraticOuterCoupling m kappa observed *
      (signedInteractionTensor m 3
        (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex) *
      ((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex) *
      signedFirstPicardCoordinateBranchStaticCoefficient
        m kappa radius (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term)
  else 0

/-- Random signed-frame static weight for an iid positive-mass ensemble. -/
def actualSignedIteratedA2StaticWeightSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) : Complex :=
  signedIteratedQuadraticSecondPicardStaticCoefficient
    (ensemble.restrictPositiveMass (N := N) sample) kappa
    (radius sample) observed term

/-! ## Measurability -/

theorem measurable_modeFrequency_of_mass_coordinates
    {Omega : Type*} [MeasurableSpace Omega]
    {N : Nat} [NeZero N]
    (massSample : Omega -> Lattice.PositiveMassConfig N)
    (hmass : forall site, Measurable fun sample => (massSample sample).mass site)
    (mode : Lattice.Site N) :
    Measurable fun sample => modeFrequency (massSample sample) mode := by
  have hmatrix : Measurable fun sample =>
      harmonicHermitian (massSample sample) := by
    apply Measurable.subtype_mk
    exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
  let ordered := (orderedIndexEquiv (ι := Lattice.Site N)).symm mode
  have hordered : Measurable fun sample =>
      orderedModeFrequency (harmonicHermitian (massSample sample)) ordered :=
    (measurable_orderedModeFrequencies_unconditional
      (fun sample => harmonicHermitian (massSample sample)) hmatrix).eval
  simpa [ordered, orderedModeFrequency_harmonicHermitian_eq] using hordered

theorem measurable_signedBondModeCoefficientSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (bond mode : Lattice.Site N) :
    Measurable fun sample =>
      signedBondModeCoefficient
        (ensemble.restrictPositiveMass (N := N) sample) bond mode := by
  have hB := measurable_massWeightedDifferenceMatrix_of_coordinate
    (ensemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate ensemble)
  have hv := measurable_orderedEigenvectorSample ensemble
    ((orderedIndexEquiv (ι := Lattice.Site N)).symm mode)
  unfold signedBondModeCoefficient Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro site _hsite
  exact ((measurable_pi_apply site).comp
      ((measurable_pi_apply bond).comp hB)).mul
    ((measurable_pi_apply site).comp hv)

theorem measurable_signedInteractionTensorSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N n : Nat} [NeZero N] (modes : Fin n -> Lattice.Site N) :
    Measurable fun sample =>
      signedInteractionTensor
        (ensemble.restrictPositiveMass (N := N) sample) n modes := by
  unfold signedInteractionTensor
  apply Finset.measurable_sum
  intro bond _hbond
  apply Finset.measurable_prod
  intro r _hr
  exact measurable_signedBondModeCoefficientSample ensemble bond (modes r)

theorem measurable_signedQuadraticPhaseCoefficientSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall mode, Measurable fun sample => radius sample mode)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    Measurable fun sample =>
      signedQuadraticPhaseCoefficient
        (ensemble.restrictPositiveMass (N := N) sample) observed
        (radius sample) term := by
  unfold signedQuadraticPhaseCoefficient
  exact ((Complex.measurable_ofReal.comp
      (measurable_signedInteractionTensorSample ensemble
        (Fin.cons observed term.1))).mul
      (Complex.measurable_ofReal.comp ((hradius (term.1 0)).div_const 2))).mul
    (Complex.measurable_ofReal.comp ((hradius (term.1 1)).div_const 2))

theorem measurable_signedFreeQuadraticDuhamelCoefficientSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall mode, Measurable fun sample => radius sample mode)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    Measurable fun sample =>
      signedFreeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling
          (ensemble.restrictPositiveMass (N := N) sample) kappa 1 observed)
        (ensemble.restrictPositiveMass (N := N) sample) observed
        (radius sample) term := by
  have hfrequency := measurable_modeFrequency_of_mass_coordinates
    (ensemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate ensemble) observed
  have hcoupling : Measurable fun sample =>
      physlibQuadraticCoupling
        (ensemble.restrictPositiveMass (N := N) sample) kappa 1 observed := by
    unfold physlibQuadraticCoupling forcedModeSource
    fun_prop
  exact hcoupling.mul
    (measurable_signedQuadraticPhaseCoefficientSample
      ensemble radius hradius observed term)

theorem measurable_signedFirstPicardCoordinateBranchStaticCoefficientSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall mode, Measurable fun sample => radius sample mode)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    Measurable fun sample =>
      signedFirstPicardCoordinateBranchStaticCoefficient
        (ensemble.restrictPositiveMass (N := N) sample) kappa
        (radius sample) innerObserved entry := by
  have hfrequency := measurable_modeFrequency_of_mass_coordinates
    (ensemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate ensemble) innerObserved
  have hscale : Measurable fun sample =>
      physlibQuadraticFirstPicardCoordinateScale
        (ensemble.restrictPositiveMass (N := N) sample) innerObserved := by
    unfold physlibQuadraticFirstPicardCoordinateScale
    fun_prop
  have hfree := measurable_signedFreeQuadraticDuhamelCoefficientSample
    ensemble kappa radius hradius innerObserved entry.1
  unfold signedFirstPicardCoordinateBranchStaticCoefficient
  apply Measurable.ite (measurableSet_Ioi.preimage hfrequency)
  · apply (Complex.measurable_ofReal.comp (hscale.div_const 2)).mul
    by_cases hbranch : entry.2 = 0
    · simpa [hbranch] using hfree
    · simp only [hbranch, if_false]
      change Measurable ((starRingEnd Complex) ∘ fun sample =>
        signedFreeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling
            (ensemble.restrictPositiveMass (N := N) sample)
            kappa 1 innerObserved)
          (ensemble.restrictPositiveMass (N := N) sample)
          innerObserved (radius sample) entry.1)
      exact Complex.continuous_conj.measurable.comp hfree
  · exact measurable_const

theorem measurable_actualSignedIteratedA2StaticWeightSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall mode, Measurable fun sample => radius sample mode)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Measurable
      (actualSignedIteratedA2StaticWeightSample ensemble kappa radius
        observed term) := by
  have hfrequency := measurable_modeFrequency_of_mass_coordinates
    (ensemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate ensemble) observed
  have hcoupling : Measurable fun sample =>
      physlibIteratedQuadraticOuterCoupling
        (ensemble.restrictPositiveMass (N := N) sample) kappa observed := by
    unfold physlibIteratedQuadraticOuterCoupling forcedModeSource
    fun_prop
  have htensor := measurable_signedInteractionTensorSample ensemble
    (Fin.cons observed (iteratedQuadraticOuterModes term))
  have hrfree := hradius (iteratedQuadraticFreeMode term)
  have hinner :=
    measurable_signedFirstPicardCoordinateBranchStaticCoefficientSample
      ensemble kappa radius hradius
      (iteratedQuadraticFirstPicardMode term)
      (iteratedQuadraticInnerEntry term)
  unfold actualSignedIteratedA2StaticWeightSample
    signedIteratedQuadraticSecondPicardStaticCoefficient
  apply Measurable.ite (measurableSet_Ioi.preimage hfrequency)
  · exact (((hcoupling.mul (Complex.measurable_ofReal.comp htensor)).mul
      (Complex.measurable_ofReal.comp (hrfree.div_const 2))).mul hinner)
  · exact measurable_const

/-! ## Exact orientation relation on simple spectrum -/

/-- Orientation of one legacy Physlib mode relative to the measurable signed
ordered frame.  It is pointwise `+1` or `-1` on simple spectrum, but it is not
claimed measurable. -/
def physlibModeOrientation {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mode : Lattice.Site N) : Real :=
  orderedPhyslibOrientation m
    ((orderedIndexEquiv (ι := Lattice.Site N)).symm mode)

/-- Product of the orientation signs carried by one tensor. -/
def tensorOrientationProduct {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n -> Lattice.Site N) : Real :=
  ∏ r, physlibModeOrientation m (modes r)

theorem signedBondModeCoefficient_eq_orientation_mul
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond mode : Lattice.Site N) :
    signedBondModeCoefficient m bond mode =
      physlibModeOrientation m mode * bondModeCoefficient m bond mode := by
  unfold signedBondModeCoefficient physlibModeOrientation bondModeCoefficient
  rw [signedOrderedEigenvector_eq_orientation_smul_normalModeBasis
    m hsimple]
  rw [Matrix.mulVec_smul]
  simp [orderedPhyslibModeIndex]

theorem signedInteractionTensor_eq_orientationProduct_mul
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (modes : Fin n -> Lattice.Site N) :
    signedInteractionTensor m n modes =
      tensorOrientationProduct m modes * interactionTensor m n modes := by
  classical
  unfold signedInteractionTensor tensorOrientationProduct interactionTensor
  simp_rw [signedBondModeCoefficient_eq_orientation_mul m hsimple]
  calc
    (∑ bond, ∏ r,
        physlibModeOrientation m (modes r) *
          bondModeCoefficient m bond (modes r)) =
        ∑ bond, (∏ r, physlibModeOrientation m (modes r)) *
          ∏ r, bondModeCoefficient m bond (modes r) := by
      apply Finset.sum_congr rfl
      intro bond _hbond
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [Finset.mul_sum]

theorem signedQuadraticPhaseCoefficient_eq_orientationProduct_mul
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (observed : Lattice.Site N) (radius : Lattice.Site N -> Real)
    (term : QuadraticPhaseTerm N) :
    signedQuadraticPhaseCoefficient m observed radius term =
      (tensorOrientationProduct m (Fin.cons observed term.1) : Complex) *
        quadraticPhaseCoefficient m observed radius term := by
  unfold signedQuadraticPhaseCoefficient quadraticPhaseCoefficient
  rw [signedInteractionTensor_eq_orientationProduct_mul m hsimple]
  push_cast
  ring

theorem signedFreeQuadraticDuhamelCoefficient_eq_orientationProduct_mul
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (coupling : Complex) (observed : Lattice.Site N)
    (radius : Lattice.Site N -> Real) (term : QuadraticPhaseTerm N) :
    signedFreeQuadraticDuhamelCoefficient coupling m observed radius term =
      (tensorOrientationProduct m (Fin.cons observed term.1) : Complex) *
        freeQuadraticDuhamelCoefficient coupling m observed radius term := by
  unfold signedFreeQuadraticDuhamelCoefficient
    freeQuadraticDuhamelCoefficient
  rw [signedQuadraticPhaseCoefficient_eq_orientationProduct_mul
    m hsimple]
  ring

theorem signedFirstPicardCoordinateBranchStaticCoefficient_eq_orientationProduct_mul
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (radius : Lattice.Site N -> Real)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    signedFirstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved entry =
      (tensorOrientationProduct m
          (Fin.cons innerObserved entry.1.1) : Complex) *
        firstPicardCoordinateBranchStaticCoefficient
          m kappa radius innerObserved entry := by
  unfold signedFirstPicardCoordinateBranchStaticCoefficient
    firstPicardCoordinateBranchStaticCoefficient
  by_cases hfrequency : 0 < modeFrequency m innerObserved
  · rw [if_pos hfrequency, if_pos hfrequency]
    rw [signedFreeQuadraticDuhamelCoefficient_eq_orientationProduct_mul
      m hsimple]
    by_cases hbranch : entry.2 = 0
    · simp only [hbranch, if_true]
      ring
    · simp only [hbranch, if_false, map_mul]
      rw [Complex.conj_ofReal]
      ring
  · rw [if_neg hfrequency, if_neg hfrequency]
    simp

theorem signedIteratedQuadraticSecondPicardStaticCoefficient_eq_orientationProducts_mul
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (radius : Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    signedIteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term =
      ((tensorOrientationProduct m
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        tensorOrientationProduct m
          (Fin.cons (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1.1) : Real) : Complex) *
        iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term := by
  unfold signedIteratedQuadraticSecondPicardStaticCoefficient
    iteratedQuadraticSecondPicardStaticCoefficient
  by_cases hfrequency : 0 < modeFrequency m observed
  · rw [if_pos hfrequency, if_pos hfrequency]
    rw [signedInteractionTensor_eq_orientationProduct_mul m hsimple]
    rw [signedFirstPicardCoordinateBranchStaticCoefficient_eq_orientationProduct_mul
      m hsimple]
    push_cast
    ring
  · rw [if_neg hfrequency, if_neg hfrequency]
    simp

theorem abs_physlibModeOrientation
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (mode : Lattice.Site N) :
    |physlibModeOrientation m mode| = 1 := by
  exact abs_orderedPhyslibOrientation m hsimple
    ((orderedIndexEquiv (ι := Lattice.Site N)).symm mode)

theorem abs_tensorOrientationProduct
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (modes : Fin n -> Lattice.Site N) :
    |tensorOrientationProduct m modes| = 1 := by
  classical
  unfold tensorOrientationProduct
  rw [Finset.abs_prod]
  simp [abs_physlibModeOrientation m hsimple]

theorem norm_signedIteratedQuadraticSecondPicardStaticCoefficient_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (radius : Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ‖signedIteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term‖ =
      ‖iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term‖ := by
  rw [signedIteratedQuadraticSecondPicardStaticCoefficient_eq_orientationProducts_mul
    m hsimple]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_tensorOrientationProduct m hsimple,
    abs_tensorOrientationProduct m hsimple]
  simp

/-! ## Almost-sure adapter and integrability -/

theorem actualSignedIteratedA2StaticWeightSample_eq_orientationProducts_mul_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N) (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ∀ᵐ aeSample ∂ensemble.probability,
      actualSignedIteratedA2StaticWeightSample ensemble kappa radius
          observed term aeSample =
        ((tensorOrientationProduct
            (ensemble.restrictPositiveMass (N := N) aeSample)
            (Fin.cons observed (iteratedQuadraticOuterModes term)) *
          tensorOrientationProduct
            (ensemble.restrictPositiveMass (N := N) aeSample)
            (Fin.cons (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term).1.1) : Real) : Complex) *
          actualIteratedA2StaticWeightSample ensemble kappa radius
            observed term aeSample := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with sample hsimple
  exact signedIteratedQuadraticSecondPicardStaticCoefficient_eq_orientationProducts_mul
    (ensemble.restrictPositiveMass (N := N) sample) hsimple kappa
    (radius sample) observed term

theorem norm_actualSignedIteratedA2StaticWeightSample_eq_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N) (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ∀ᵐ aeSample ∂ensemble.probability,
      ‖actualSignedIteratedA2StaticWeightSample ensemble kappa radius
          observed term aeSample‖ =
        ‖actualIteratedA2StaticWeightSample ensemble kappa radius
          observed term aeSample‖ := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with sample hsimple
  exact norm_signedIteratedQuadraticSecondPicardStaticCoefficient_eq
    (ensemble.restrictPositiveMass (N := N) sample) hsimple kappa
    (radius sample) observed term

/-- Unlike the legacy coefficient, the signed-frame replacement is
integrable from measurable radius coordinates alone. -/
theorem integrable_actualSignedIteratedA2StaticWeightSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 <= N)
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradiusMeasurable : forall mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Integrable
      (actualSignedIteratedA2StaticWeightSample ensemble kappa radius
        observed term) ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  apply Integrable.of_bound
    (measurable_actualSignedIteratedA2StaticWeightSample
      ensemble kappa radius hradiusMeasurable observed term).aestronglyMeasurable
    (4 * |kappa| ^ 2 * R ^ 3)
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with sample hsimple
  unfold actualSignedIteratedA2StaticWeightSample
  rw [norm_signedIteratedQuadraticSecondPicardStaticCoefficient_eq
    (ensemble.restrictPositiveMass (N := N) sample) hsimple]
  exact norm_actualIteratedA2StaticWeightSample_le ensemble kappa R hR radius
    hradiusBound observed term sample

end

end CanonicalIIDCoerciveIteratedA2MeasurableSignedStaticWeight
end ArchonPhysics
