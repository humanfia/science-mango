import ArchonPhysics.BondPotentialHamiltonianPhyslib
import ArchonPhysics.MassWeightedHamiltonianDynamics
import ArchonPhysics.PhyslibHamiltonDerivativeBridge
import ArchonPhysics.ForcedComplexModeDuhamel

/-!
# Exact Lennard--Jones Hamilton trajectory to modal Duhamel formula

For the equilibrium-distance Lennard--Jones bond, this module makes the exact
force split

`V'_LJ(x) = k_LJ * x + R_LJ(x)`,  `k_LJ = 72 * depth / r₀^2`,

and lifts it through the finite bond gradient, mass weighting, the random-mass
normal-mode transform, and the interaction-picture Duhamel formula.  The
residual is the full inverse-power remainder, not a truncated Taylor
polynomial, so every identity below is exact on a supplied nonsingular
trajectory.

Nonsingularity of every actual bond length is an explicit trajectory
hypothesis.  It is not proved here and therefore this module makes no
collision-avoidance or global-existence claim.  It also makes no random-phase
propagation, stochastic closure, microscopic-to-kinetic limit, or
thermalization claim.
-/

namespace ArchonPhysics.LennardJonesHamiltonianDuhamel

open Set
open Time
open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalForcedDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- The exact LJ force residual after subtracting its equilibrium harmonic
part.  This retains every inverse-power term of the original potential. -/
def lennardJonesResidualDerivative (depth r₀ x : Real) : Real :=
  lennardJonesDerivative depth r₀ x -
    LennardJonesPotential.harmonicStiffness depth r₀ * x

/-- The harmonic stiffness appearing in the exact force decomposition is
`72 * depth / r₀^2`. -/
theorem harmonicStiffness_eq (depth r₀ : Real) :
    LennardJonesPotential.harmonicStiffness depth r₀ =
      72 * depth / r₀ ^ 2 := by
  rfl

/-- Exact one-bond LJ force decomposition; this is algebraic, not a Taylor
approximation. -/
theorem lennardJonesDerivative_eq_harmonic_add_residual
    (depth r₀ x : Real) :
    lennardJonesDerivative depth r₀ x =
      LennardJonesPotential.harmonicStiffness depth r₀ * x +
        lennardJonesResidualDerivative depth r₀ x := by
  unfold lennardJonesResidualDerivative
  ring

/-- The finite residual bond gradient obtained directly by summing the exact
LJ force residual over all periodic bonds. -/
def lennardJonesResidualGradient {N : Nat} [NeZero N]
    (depth r₀ : Real) (q : HilbertConfiguration N) :
    HilbertConfiguration N :=
  BondPotentialHamiltonianPhyslib.potentialGradient
    (lennardJonesResidualDerivative depth r₀) q

/-- The full finite LJ potential gradient is exactly the stiffness-scaled
harmonic gradient plus the explicit finite residual gradient. -/
theorem potentialGradient_lennardJones_eq_harmonic_add_residual
    {N : Nat} [NeZero N] (depth r₀ : Real)
    (q : HilbertConfiguration N) :
    BondPotentialHamiltonianPhyslib.potentialGradient
        (lennardJonesDerivative depth r₀) q =
      LennardJonesPotential.harmonicStiffness depth r₀ •
          harmonicPotentialGradient q +
        lennardJonesResidualGradient depth r₀ q := by
  classical
  unfold lennardJonesResidualGradient harmonicPotentialGradient
    BondPotentialHamiltonianPhyslib.potentialGradient
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lennardJonesDerivative_eq_harmonic_add_residual, add_smul,
    smul_smul]

/-- The exact LJ residual force in mass-weighted configuration coordinates,
including the Hamiltonian minus sign. -/
def transformedLennardJonesResidualForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (q : HilbertConfiguration N) : WeightedConfiguration N :=
  -inverseSqrtMassTransform m
    (lennardJonesResidualGradient depth r₀ q)

/-- After mass weighting, the exact LJ force is a stiffness-scaled harmonic
operator plus the independently defined full inverse-power residual force. -/
theorem transformedLennardJonesForce_eq_harmonic_add_residual
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (q : HilbertConfiguration N) :
    inverseSqrtMassTransform m
        (-BondPotentialHamiltonianPhyslib.potentialGradient
          (lennardJonesDerivative depth r₀) q) =
      -(LennardJonesPotential.harmonicStiffness depth r₀ •
          harmonicOperator m (sqrtMassTransform m q)) +
        transformedLennardJonesResidualForce m depth r₀ q := by
  rw [potentialGradient_lennardJones_eq_harmonic_add_residual]
  simp only [map_neg, map_add, map_smul,
    inverseSqrtMassTransform_harmonicPotentialGradient]
  unfold transformedLennardJonesResidualForce
  abel

/-- Real-parameter derivative witnesses for the exact nonsingular LJ
Hamilton equations. -/
def HasExplicitLennardJonesHamiltonDerivatives
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Real → HilbertConfiguration N) : Prop :=
  ∀ tau,
    HasDerivAt q (inverseMassMomentum m (p tau)) tau ∧
      HasDerivAt p
        (-BondPotentialHamiltonianPhyslib.potentialGradient
          (lennardJonesDerivative depth r₀) (q tau)) tau

/-- A differentiable Physlib LJ trajectory, together with explicit
nonsingularity of every occupied bond, supplies the real-parameter derivative
witnesses used below. -/
theorem hasExplicitLennardJonesHamiltonDerivatives_of_physlib
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : BondPotentialHamiltonianPhyslib.SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t)) :
    HasExplicitLennardJonesHamiltonDerivatives m depth r₀
      (realReparametrize p) (realReparametrize q) := by
  have hExplicit :=
    (lennardJones_satisfiesHamiltonEquations_iff_explicit
      m depth r₀ p q hnonsingular).mp hHamilton
  intro tau
  let t : Time := Time.toRealCLE.symm tau
  constructor
  · have hqDeriv := hasDerivAt_comp_toRealCLE_symm q tau (hq t)
    rw [hExplicit.1 t] at hqDeriv
    exact hqDeriv
  · have hpDeriv := hasDerivAt_comp_toRealCLE_symm p tau (hp t)
    rw [hExplicit.2 t] at hpDeriv
    exact hpDeriv

/-- Exact mass-weighted forced harmonic equations obtained from explicit LJ
Hamilton derivative witnesses. -/
theorem massWeightedLennardJonesEquations_of_explicitDerivatives
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    {p q : Real → HilbertConfiguration N}
    (hDynamics : HasExplicitLennardJonesHamiltonDerivatives
      m depth r₀ p q) (tau : Real) :
    HasMassWeightedDerivAt (massWeightedPosition m q)
        (massWeightedMomentum m p tau) tau ∧
      HasMassWeightedDerivAt (massWeightedMomentum m p)
        (-(LennardJonesPotential.harmonicStiffness depth r₀ •
            harmonicOperator m (massWeightedPosition m q tau)) +
          transformedLennardJonesResidualForce m depth r₀ (q tau)) tau := by
  constructor
  · have hX := (sqrtMassTransform m).hasFDerivAt.comp_hasDerivAt
      tau (hDynamics tau).1
    change HasMassWeightedDerivAt (fun s => sqrtMassTransform m (q s))
      (inverseSqrtMassTransform m (p tau)) tau
    simpa only [HasMassWeightedDerivAt, Function.comp_def,
      sqrtMassTransform_inverseMassMomentum] using hX
  · have hY := (inverseSqrtMassTransform m).hasFDerivAt.comp_hasDerivAt
      tau (hDynamics tau).2
    change HasMassWeightedDerivAt
      (fun s => inverseSqrtMassTransform m (p s))
      (-(LennardJonesPotential.harmonicStiffness depth r₀ •
          harmonicOperator m (sqrtMassTransform m (q tau))) +
        transformedLennardJonesResidualForce m depth r₀ (q tau)) tau
    simpa only [HasMassWeightedDerivAt, Function.comp_def,
      transformedLennardJonesForce_eq_harmonic_add_residual] using hY

/-- Exact mass-weighted LJ equations for an actual differentiable Physlib
trajectory on which every physical bond remains nonsingular. -/
theorem massWeightedLennardJonesEquations_of_physlib
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : BondPotentialHamiltonianPhyslib.SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t))
    (tau : Real) :
    HasMassWeightedDerivAt
        (massWeightedPosition m (realReparametrize q))
        (massWeightedMomentum m (realReparametrize p) tau) tau ∧
      HasMassWeightedDerivAt
        (massWeightedMomentum m (realReparametrize p))
        (-(LennardJonesPotential.harmonicStiffness depth r₀ •
            harmonicOperator m
              (massWeightedPosition m (realReparametrize q) tau)) +
          transformedLennardJonesResidualForce m depth r₀
            (realReparametrize q tau)) tau := by
  exact massWeightedLennardJonesEquations_of_explicitDerivatives
    m depth r₀
    (hasExplicitLennardJonesHamiltonDerivatives_of_physlib
      m depth r₀ p q hp hq hHamilton hnonsingular) tau

/-- The exact harmonic frequency of mode `k` after restoring the LJ
stiffness. -/
def lennardJonesModeFrequency {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N) : Real :=
  Real.sqrt (LennardJonesPotential.harmonicStiffness depth r₀) *
    modeFrequency m k

/-- Squaring the scaled mode frequency restores the stiffness-scaled harmonic
eigenvalue. -/
theorem lennardJonesModeFrequency_sq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N)
    (hstiff : 0 ≤ LennardJonesPotential.harmonicStiffness depth r₀) :
    lennardJonesModeFrequency m depth r₀ k ^ 2 =
      LennardJonesPotential.harmonicStiffness depth r₀ *
        modeFrequency m k ^ 2 := by
  unfold lennardJonesModeFrequency
  rw [mul_pow, Real.sq_sqrt hstiff]

/-- Positive physical LJ parameters give positive harmonic stiffness. -/
theorem harmonicStiffness_pos {depth r₀ : Real}
    (hdepth : 0 < depth) (hr₀ : r₀ ≠ 0) :
    0 < LennardJonesPotential.harmonicStiffness depth r₀ := by
  unfold LennardJonesPotential.harmonicStiffness
  exact div_pos (mul_pos (by norm_num) hdepth) (sq_pos_of_ne_zero hr₀)

/-- A positive unscaled mode remains positive after restoring positive LJ
stiffness. -/
theorem lennardJonesModeFrequency_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    {depth r₀ : Real} (hdepth : 0 < depth) (hr₀ : r₀ ≠ 0)
    (hmode : 0 < modeFrequency m k) :
    0 < lennardJonesModeFrequency m depth r₀ k := by
  unfold lennardJonesModeFrequency
  exact mul_pos (Real.sqrt_pos.2 (harmonicStiffness_pos hdepth hr₀)) hmode

/-- Mass-weighted position of one LJ normal mode along a Physlib trajectory. -/
def physlibModePosition {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (q : Time → HilbertConfiguration N) : Real → Real :=
  fun tau => modalCoordinates m
    (massWeightedPosition m (realReparametrize q) tau) k

/-- Mass-weighted momentum of one LJ normal mode along a Physlib trajectory. -/
def physlibModeMomentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (p : Time → HilbertConfiguration N) : Real → Real :=
  fun tau => modalCoordinates m
    (massWeightedMomentum m (realReparametrize p) tau) k

/-- Modal projection of the exact full inverse-power LJ residual force. -/
def physlibModeResidualForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N) :
    Real → Real :=
  fun tau => modalCoordinates m
    (transformedLennardJonesResidualForce m depth r₀
      (realReparametrize q tau)) k

/-- The exact mass-weighted LJ equations project to a scalar forced
oscillator of frequency `sqrt(k_LJ) * omega_k`. -/
theorem modeEquations_of_physlib
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : BondPotentialHamiltonianPhyslib.SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t))
    (hstiff : 0 ≤ LennardJonesPotential.harmonicStiffness depth r₀)
    (tau : Real) :
    HasDerivAt (physlibModePosition m k q)
        (physlibModeMomentum m k p tau) tau ∧
      HasDerivAt (physlibModeMomentum m k p)
        (-(lennardJonesModeFrequency m depth r₀ k) ^ 2 *
            physlibModePosition m k q tau +
          physlibModeResidualForce m depth r₀ k q tau) tau := by
  unfold physlibModePosition physlibModeMomentum physlibModeResidualForce
  have hWeighted := massWeightedLennardJonesEquations_of_physlib
    m depth r₀ p q hp hq hHamilton hnonsingular tau
  have hX := hWeighted.1
  have hY := hWeighted.2
  simp only [HasMassWeightedDerivAt] at hX hY
  constructor
  · exact hasDerivAt_modalCoordinate m k hX
  · have hYmodal := hasDerivAt_modalCoordinate m k
      (X := massWeightedMomentum m (realReparametrize p))
      (V := fun s =>
        -(LennardJonesPotential.harmonicStiffness depth r₀ •
            harmonicOperator m
              (massWeightedPosition m (realReparametrize q) s)) +
          transformedLennardJonesResidualForce m depth r₀
            (realReparametrize q s)) hY
    convert hYmodal using 1
    simp only [map_add, map_neg, map_smul, WithLp.ofLp_add,
      WithLp.ofLp_neg, WithLp.ofLp_smul, Pi.add_apply, Pi.neg_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [modalCoordinates_harmonicOperator, ← modeFrequency_sq,
      lennardJonesModeFrequency_sq m depth r₀ k hstiff]
    ring

/-- Positive-frequency complex amplitude of one exact LJ normal mode. -/
def physlibModeAmplitude {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N) : Real → Complex :=
  fun tau => complexModeAmplitude (lennardJonesModeFrequency m depth r₀ k)
    (physlibModePosition m k q tau) (physlibModeMomentum m k p tau)

/-- Exact LJ residual source after removal of the free mode rotation. -/
def physlibModeRotatedSource {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N) :
    Real → Complex :=
  fun tau =>
    phaseFactor (lennardJonesModeFrequency m depth r₀ k * tau) *
      forcedModeSource (lennardJonesModeFrequency m depth r₀ k)
        (physlibModeResidualForce m depth r₀ k q tau)

/-- The scalar forced-oscillator equation gives the exact pointwise complex
mode equation for an actual nonsingular LJ trajectory. -/
theorem hasDerivAt_physlibModeAmplitude
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : BondPotentialHamiltonianPhyslib.SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t))
    (hstiff : 0 ≤ LennardJonesPotential.harmonicStiffness depth r₀)
    (homega : 0 < lennardJonesModeFrequency m depth r₀ k)
    (tau : Real) :
    HasDerivAt (physlibModeAmplitude m depth r₀ k p q)
      (forcedModeSource (lennardJonesModeFrequency m depth r₀ k)
          (physlibModeResidualForce m depth r₀ k q tau) -
        (Complex.I *
          (lennardJonesModeFrequency m depth r₀ k : Complex)) *
          physlibModeAmplitude m depth r₀ k p q tau) tau := by
  have hMode := modeEquations_of_physlib
    m depth r₀ k p q hp hq hHamilton hnonsingular hstiff tau
  unfold physlibModeAmplitude
  exact hasDerivAt_complexModeAmplitude_forced homega hMode.1 hMode.2

/-- A differentiable Physlib curve is continuous after canonical
real-parameter reparametrization. -/
theorem continuous_realReparametrize
    {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
    (w : Time → E) (hw : Differentiable Real w) :
    Continuous (realReparametrize w) := by
  unfold realReparametrize
  exact hw.continuous.comp Time.toRealCLE.symm.continuous

/-- The exact LJ force residual is continuous at every nonsingular bond
displacement. -/
theorem continuousAt_lennardJonesResidualDerivative
    {depth r₀ x : Real} (hnonsingular : r₀ + x ≠ 0) :
    ContinuousAt (lennardJonesResidualDerivative depth r₀) x := by
  have hinner : ContinuousAt (fun y : Real => r₀ + y) x :=
    continuousAt_const.add continuousAt_id
  have hradial : ContinuousAt
      (fun y : Real =>
        LennardJonesPotential.radialDerivative depth r₀ (r₀ + y)) x := by
    exact (LennardJonesPotential.hasDerivAt_radialDerivative
      hnonsingular).continuousAt.comp hinner
  exact hradial.sub (continuousAt_const.mul continuousAt_id)

/-- Along a continuous nonsingular physical path, the exact residual on one
fixed bond is continuous. -/
theorem continuous_lennardJonesResidualDerivative_bond
    {N : Nat} [NeZero N]
    (depth r₀ : Real) (i : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (hq : Differentiable Real q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t)) :
    Continuous (fun tau =>
      lennardJonesResidualDerivative depth r₀
        (Lattice.forwardDifference
          (asConfiguration (realReparametrize q tau)) i)) := by
  have hpath : Continuous (realReparametrize q) :=
    continuous_realReparametrize q hq
  have hbond : Continuous (fun tau =>
      Lattice.forwardDifference
        (asConfiguration (realReparametrize q tau)) i) := by
    simpa only [Function.comp_apply, bondFunctional_apply] using
      (bondFunctional i).continuous.comp' hpath
  rw [continuous_iff_continuousAt]
  intro tau
  have hnon : r₀ + Lattice.forwardDifference
      (asConfiguration (realReparametrize q tau)) i ≠ 0 := by
    exact hnonsingular (Time.toRealCLE.symm tau) i
  exact ContinuousAt.comp'
    (f := fun s => Lattice.forwardDifference
      (asConfiguration (realReparametrize q s)) i)
    (g := lennardJonesResidualDerivative depth r₀)
    (continuousAt_lennardJonesResidualDerivative hnon)
    hbond.continuousAt

/-- The finite mass-weighted exact LJ residual force is continuous along a
differentiable nonsingular trajectory. -/
theorem continuous_transformedLennardJonesResidualForce
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (q : Time → HilbertConfiguration N) (hq : Differentiable Real q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t)) :
    Continuous (fun tau =>
      transformedLennardJonesResidualForce m depth r₀
        (realReparametrize q tau)) := by
  have hgradient : Continuous (fun tau =>
      lennardJonesResidualGradient depth r₀
        (realReparametrize q tau)) := by
    unfold lennardJonesResidualGradient
      BondPotentialHamiltonianPhyslib.potentialGradient
    apply continuous_finsetSum Finset.univ
    intro i hi
    exact (continuous_lennardJonesResidualDerivative_bond
      depth r₀ i q hq hnonsingular).smul continuous_const
  unfold transformedLennardJonesResidualForce
  simpa only [Pi.neg_apply, map_neg] using
    (inverseSqrtMassTransform m).continuous.comp' hgradient.neg

/-- The modal residual force is continuous along a differentiable
nonsingular LJ trajectory. -/
theorem continuous_physlibModeResidualForce
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t)) :
    Continuous (physlibModeResidualForce m depth r₀ k q) := by
  unfold physlibModeResidualForce
  exact (modalCoordinateCLM m k).continuous.comp
    (continuous_transformedLennardJonesResidualForce
      m depth r₀ q hq hnonsingular)

/-- The real-angle complex phase factor is continuous. -/
theorem continuous_phaseFactor_real : Continuous phaseFactor := by
  unfold phaseFactor
  exact Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal)

/-- A continuous real force yields a continuous complex forced-mode source
at fixed frequency. -/
theorem continuous_forcedModeSource_comp
    (omega : Real) {force : Real → Real} (hforce : Continuous force) :
    Continuous (fun tau => forcedModeSource omega (force tau)) := by
  unfold forcedModeSource
  exact (continuous_const.mul
    (Complex.continuous_ofReal.comp hforce)).div_const _

/-- The exact interaction-picture LJ residual source is continuous along a
differentiable nonsingular physical path. -/
theorem continuous_physlibModeRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t)) :
    Continuous (physlibModeRotatedSource m depth r₀ k q) := by
  unfold physlibModeRotatedSource
  exact (continuous_phaseFactor_real.comp
      (continuous_const.mul continuous_id)).mul
    (continuous_forcedModeSource_comp
      (lennardJonesModeFrequency m depth r₀ k)
      (continuous_physlibModeResidualForce
        m depth r₀ k q hq hnonsingular))

/-- Consequently the exact rotated LJ source is integrable on every finite
oriented interval, under the explicit all-time nonsingularity hypothesis. -/
theorem intervalIntegrable_physlibModeRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N) (q : Time → HilbertConfiguration N)
    (hq : Differentiable Real q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t))
    (a b : Real) :
    IntervalIntegrable (physlibModeRotatedSource m depth r₀ k q)
      MeasureTheory.volume a b := by
  exact (continuous_physlibModeRotatedSource
    m depth r₀ k q hq hnonsingular).intervalIntegrable a b

/-- Exact finite-time interaction-picture Duhamel identity for one selected
positive-frequency mode of an actual nonsingular LJ Hamilton trajectory. -/
theorem interactionPicture_physlibMode_eq_initial_add_integral
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : BondPotentialHamiltonianPhyslib.SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t))
    (hstiff : 0 ≤ LennardJonesPotential.harmonicStiffness depth r₀)
    (homega : 0 < lennardJonesModeFrequency m depth r₀ k) (t : Real)
    (hIntegrable : IntervalIntegrable
      (physlibModeRotatedSource m depth r₀ k q)
      MeasureTheory.volume 0 t) :
    phaseRenormalize (lennardJonesModeFrequency m depth r₀ k * t)
        (physlibModeAmplitude m depth r₀ k p q t) =
      physlibModeAmplitude m depth r₀ k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m depth r₀ k q s := by
  apply interactionPicture_forcedMode_eq_initial_add_integral homega
  · intro s hs
    exact (modeEquations_of_physlib m depth r₀ k p q hp hq hHamilton
      hnonsingular hstiff s).1
  · intro s hs
    exact (modeEquations_of_physlib m depth r₀ k p q hp hq hHamilton
      hnonsingular hstiff s).2
  · unfold physlibModeRotatedSource at hIntegrable
    exact hIntegrable

/-- Exact finite-time LJ Duhamel identity with source integrability discharged
from differentiability and the supplied all-time nonsingularity condition. -/
theorem interactionPicture_physlibMode_eq_initial_add_integral_of_nonsingular
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (k : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : BondPotentialHamiltonianPhyslib.SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t))
    (hstiff : 0 ≤ LennardJonesPotential.harmonicStiffness depth r₀)
    (homega : 0 < lennardJonesModeFrequency m depth r₀ k) (t : Real) :
    phaseRenormalize (lennardJonesModeFrequency m depth r₀ k * t)
        (physlibModeAmplitude m depth r₀ k p q t) =
      physlibModeAmplitude m depth r₀ k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m depth r₀ k q s := by
  exact interactionPicture_physlibMode_eq_initial_add_integral
    m depth r₀ k p q hp hq hHamilton hnonsingular hstiff homega t
      (intervalIntegrable_physlibModeRotatedSource
        m depth r₀ k q hq hnonsingular 0 t)

end

end ArchonPhysics.LennardJonesHamiltonianDuhamel
