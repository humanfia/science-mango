import ArchonPhysics.PhyslibHamiltonDerivativeBridge
import ArchonPhysics.ForcedComplexModeDuhamel

/-!
# Exact Duhamel formula for a Physlib Hamilton trajectory

This module joins the actual Physlib Hamilton equations for the coercive
lattice Hamiltonian to the existing one-mode Duhamel adapter.  After the
canonical real-time and mass-weighted changes of variables, the nonlinear
source is exactly the previously verified three- and four-leg tensor force.

The selected mode is required to have positive frequency, so the translation
zero mode is not included.  Continuity of the finite tensor polynomial along
a differentiable trajectory proves interval integrability of the displayed
source, so the final physical-trajectory corollaries need no separate
integrability hypothesis.  No kinetic limit, stochastic averaging, resonance
closure, or thermalization statement is used here.
-/

namespace ArchonPhysics.PhyslibHamiltonDuhamel

open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Mass-weighted position of one normal mode along a Physlib trajectory. -/
def physlibModePosition {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (q : Time → HilbertConfiguration N) : Real → Real :=
  fun tau ↦ modalCoordinates m
    (massWeightedPosition m (realReparametrize q) tau) k

/-- Mass-weighted momentum of one normal mode along a Physlib trajectory. -/
def physlibModeMomentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (p : Time → HilbertConfiguration N) : Real → Real :=
  fun tau ↦ modalCoordinates m
    (massWeightedMomentum m (realReparametrize p) tau) k

/-- Exact modal nonlinear force, expressed through the verified interaction
tensor contractions. -/
def physlibModeTensorForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N) : Real → Real :=
  fun tau ↦ tensorNonlinearForce m kappa beta g
    (modalCoordinates m
      (massWeightedPosition m (realReparametrize q) tau)) k

/-- Positive-frequency complex amplitude of the selected physical mode. -/
def physlibModeAmplitude {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N) : Real → Complex :=
  fun tau ↦ complexModeAmplitude (modeFrequency m k)
    (physlibModePosition m k q tau) (physlibModeMomentum m k p tau)

/-- The exact tensor force after the free mode rotation. -/
def physlibModeRotatedSource {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N) :
    Real → Complex :=
  fun tau ↦ phaseFactor (modeFrequency m k * tau) *
    forcedModeSource (modeFrequency m k)
      (physlibModeTensorForce m kappa beta g k q tau)

/-- Differentiability of a Physlib time curve makes its canonical real-time
reparametrization continuous. -/
theorem continuous_realReparametrize
    {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
    (w : Time → E) (hw : Differentiable Real w) :
    Continuous (realReparametrize w) := by
  unfold realReparametrize
  exact hw.continuous.comp Time.toRealCLE.symm.continuous

/-- The selected mass-weighted modal position is continuous along every
differentiable Physlib configuration path. -/
theorem continuous_physlibModePosition
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (hq : Differentiable Real q) :
    Continuous (physlibModePosition m k q) := by
  unfold physlibModePosition massWeightedPosition
  exact (PiLp.continuous_apply 2 _ k).comp
    ((modalCoordinates m).continuous.comp
      ((sqrtMassTransform m).continuous.comp
        (continuous_realReparametrize q hq)))

/-- A finite interaction-tensor contraction is continuous along a continuous
modal-amplitude path. -/
theorem continuous_distinguishedTensorContraction_comp
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (amplitude : Real → WeightedConfiguration N)
    (hamplitude : Continuous amplitude) (k : Lattice.Site N) :
    Continuous (fun tau ↦
      distinguishedTensorContraction m (amplitude tau) k n) := by
  classical
  unfold distinguishedTensorContraction
  apply continuous_finsetSum Finset.univ
  intro modes _
  apply continuous_const.mul
  apply continuous_finsetProd Finset.univ
  intro r _
  exact (PiLp.continuous_apply 2 _ (modes r)).comp hamplitude

/-- The exact quadratic/cubic tensor force is continuous along a continuous
modal-amplitude path. -/
theorem continuous_tensorNonlinearForce_comp
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (amplitude : Real → WeightedConfiguration N)
    (hamplitude : Continuous amplitude) (k : Lattice.Site N) :
    Continuous (fun tau ↦ tensorNonlinearForce m kappa beta g
      (amplitude tau) k) := by
  unfold tensorNonlinearForce
  exact ((continuous_const.mul
      (continuous_distinguishedTensorContraction_comp
        m amplitude hamplitude k (n := 2))).neg).sub
    (continuous_const.mul
      (continuous_distinguishedTensorContraction_comp
        m amplitude hamplitude k (n := 3)))

/-- The exact tensor source along a differentiable physical configuration
trajectory is continuous. -/
theorem continuous_physlibModeTensorForce
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q) :
    Continuous (physlibModeTensorForce m kappa beta g k q) := by
  unfold physlibModeTensorForce
  apply continuous_tensorNonlinearForce_comp
  exact (modalCoordinates m).continuous.comp
    ((sqrtMassTransform m).continuous.comp
      (continuous_realReparametrize q hq))

/-- The real-angle complex phase factor is continuous. -/
theorem continuous_phaseFactor_real : Continuous phaseFactor := by
  unfold phaseFactor
  exact Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal)

/-- A continuous real force gives a continuous complex forced-mode source at
every fixed frequency. -/
theorem continuous_forcedModeSource_comp
    (omega : Real) {force : Real → Real} (hforce : Continuous force) :
    Continuous (fun tau ↦ forcedModeSource omega (force tau)) := by
  unfold forcedModeSource
  exact (continuous_const.mul
    (Complex.continuous_ofReal.comp hforce)).div_const _

/-- The exact tensor source after the free mode rotation is continuous along
every differentiable Physlib configuration path. -/
theorem continuous_physlibModeRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q) :
    Continuous (physlibModeRotatedSource m kappa beta g k q) := by
  unfold physlibModeRotatedSource
  exact (continuous_phaseFactor_real.comp
      (continuous_const.mul continuous_id)).mul
    (continuous_forcedModeSource_comp (modeFrequency m k)
      (continuous_physlibModeTensorForce m kappa beta g k q hq))

/-- Consequently, the exact rotated tensor source is integrable on every
finite oriented real interval. -/
theorem intervalIntegrable_physlibModeRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q) (a b : Real) :
    IntervalIntegrable (physlibModeRotatedSource m kappa beta g k q)
      MeasureTheory.volume a b := by
  exact (continuous_physlibModeRotatedSource
    m kappa beta g k q hq).intervalIntegrable a b

/-- The Physlib Hamilton equations give the first-order scalar forced
oscillator system with the exact tensor source. -/
theorem modeTensorEquations_of_physlib
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (tau : Real) :
    HasDerivAt (physlibModePosition m k q)
        (physlibModeMomentum m k p tau) tau ∧
      HasDerivAt (physlibModeMomentum m k p)
        (-(modeFrequency m k) ^ 2 * physlibModePosition m k q tau +
          physlibModeTensorForce m kappa beta g k q tau) tau := by
  unfold physlibModePosition physlibModeMomentum physlibModeTensorForce
  exact modalScalarTensorEquations_of_physlib
    m kappa beta g k p q hp hq hHamilton tau

/-- Pointwise complex forced-mode equation obtained from an actual
differentiable Physlib Hamilton trajectory. -/
theorem hasDerivAt_physlibModeAmplitude
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (tau : Real) :
    HasDerivAt (physlibModeAmplitude m k p q)
      (forcedModeSource (modeFrequency m k)
          (physlibModeTensorForce m kappa beta g k q tau) -
        (Complex.I * (modeFrequency m k : Complex)) *
          physlibModeAmplitude m k p q tau) tau := by
  have hMode := modeTensorEquations_of_physlib
    m kappa beta g k p q hp hq hHamilton tau
  unfold physlibModeAmplitude
  exact hasDerivAt_complexModeAmplitude_forced homega hMode.1 hMode.2

/-- Exact finite-time interaction-picture Duhamel identity for a selected
positive-frequency mode of the actual lattice Hamiltonian trajectory. -/
theorem interactionPicture_physlibMode_eq_initial_add_integral
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t : Real)
    (hIntegrable : IntervalIntegrable
      (physlibModeRotatedSource m kappa beta g k q)
      MeasureTheory.volume 0 t) :
    phaseRenormalize (modeFrequency m k * t)
        (physlibModeAmplitude m k p q t) =
      physlibModeAmplitude m k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m kappa beta g k q s := by
  apply interactionPicture_forcedMode_eq_initial_add_integral homega
  · intro s _
    exact (modeTensorEquations_of_physlib
      m kappa beta g k p q hp hq hHamilton s).1
  · intro s _
    exact (modeTensorEquations_of_physlib
      m kappa beta g k p q hp hq hHamilton s).2
  · unfold physlibModeRotatedSource at hIntegrable
    exact hIntegrable

/-- Exact finite-time interaction-picture Duhamel identity with source
integrability discharged from differentiability of the physical trajectory. -/
theorem interactionPicture_physlibMode_eq_initial_add_integral_of_differentiable
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t : Real) :
    phaseRenormalize (modeFrequency m k * t)
        (physlibModeAmplitude m k p q t) =
      physlibModeAmplitude m k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m kappa beta g k q s := by
  exact interactionPicture_physlibMode_eq_initial_add_integral
    m kappa beta g k p q hp hq hHamilton homega t
      (intervalIntegrable_physlibModeRotatedSource
        m kappa beta g k q hq 0 t)

/-- Equivalent Schrödinger-picture Duhamel identity for the same physical
mode and exact tensor source. -/
theorem physlibModeAmplitude_eq_inversePhase_initial_add_integral
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t : Real)
    (hIntegrable : IntervalIntegrable
      (physlibModeRotatedSource m kappa beta g k q)
      MeasureTheory.volume 0 t) :
    physlibModeAmplitude m k p q t =
      phaseRenormalize (-(modeFrequency m k * t))
        (physlibModeAmplitude m k p q 0 +
          ∫ s in 0..t, physlibModeRotatedSource m kappa beta g k q s) := by
  rw [← interactionPicture_physlibMode_eq_initial_add_integral
    m kappa beta g k p q hp hq hHamilton homega t hIntegrable]
  simp

/-- Schrödinger-picture Duhamel identity with finite-interval integrability
derived from differentiability rather than supplied as a hypothesis. -/
theorem physlibModeAmplitude_eq_inversePhase_initial_add_integral_of_differentiable
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m k) (t : Real) :
    physlibModeAmplitude m k p q t =
      phaseRenormalize (-(modeFrequency m k * t))
        (physlibModeAmplitude m k p q 0 +
          ∫ s in 0..t, physlibModeRotatedSource m kappa beta g k q s) := by
  exact physlibModeAmplitude_eq_inversePhase_initial_add_integral
    m kappa beta g k p q hp hq hHamilton homega t
      (intervalIntegrable_physlibModeRotatedSource
        m kappa beta g k q hq 0 t)

end

end ArchonPhysics.PhyslibHamiltonDuhamel
