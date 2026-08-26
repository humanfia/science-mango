import ArchonPhysics.PaperSpectralEntropyCriterion

/-!
# Faithful 2D/3D paper spectral-entropy scaling

This module formalizes the numerical criterion in *Phys. Rev. Lett.* 132,
217102 (2024), DOI `10.1103/PhysRevLett.132.217102`.

The published observable is all-mode
`xi = exp(-sum_k w_k log w_k) / card(mode)`.  It is not the upper-band-weighted
one-dimensional observable.  The published thresholds are 0.65 for the
hexagonal and FCC families and 0.95 for the square and simple-cubic families.
The numerical source uses fixed boundary conditions.

Mode types are arbitrary finite types at every finite size, so they may carry
wave-vector, polarization, and branch indices.  A branched Cartesian alias is
provided only as an optional adapter; none of the lattice-family theorems is
restricted to it.  Exact time rescaling and `HighProbabilityG2Bounds` remain
explicit inputs, not conclusions about a concrete Hamiltonian.
-/

namespace ArchonPhysics.DimensionalPaperSpectralEntropyScaling

open Filter MeasureTheory Set Topology
open scoped ENNReal
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.HamiltonianScaling
open ArchonPhysics.PaperSpectralEntropyCriterion
open ArchonPhysics.ThermalizationTransfer

noncomputable section

/-- Optional Cartesian-with-branch adapter.  The main theorems accept any
finite mode type and do not require this representation. -/
abbrev BranchedCartesianMode (dimension side branches : Nat) :=
  (Fin dimension -> Fin side) × Fin branches

/-- The lattice tag selects only published metadata, never the mode type. -/
inductive HighDimensionalLatticeKind
  | hexagonal2D
  | square2D
  | faceCenteredCubic3D
  | simpleCubic3D
  deriving DecidableEq

/-- Dimension metadata for the four lattice kinds. -/
def HighDimensionalLatticeKind.dimension : HighDimensionalLatticeKind -> Nat
  | .hexagonal2D => 2
  | .square2D => 2
  | .faceCenteredCubic3D => 3
  | .simpleCubic3D => 3

/-- Published threshold metadata, selected by lattice kind rather than only
by dimension. -/
def HighDimensionalLatticeKind.threshold :
    HighDimensionalLatticeKind -> Real
  | .hexagonal2D => 65 / 100
  | .square2D => 95 / 100
  | .faceCenteredCubic3D => 65 / 100
  | .simpleCubic3D => 95 / 100

@[simp] theorem highDimensionalThreshold_hexagonal2D :
    HighDimensionalLatticeKind.hexagonal2D.threshold = (0.65 : Real) := by
  norm_num [HighDimensionalLatticeKind.threshold]

@[simp] theorem highDimensionalThreshold_square2D :
    HighDimensionalLatticeKind.square2D.threshold = (0.95 : Real) := by
  norm_num [HighDimensionalLatticeKind.threshold]

@[simp] theorem highDimensionalThreshold_faceCenteredCubic3D :
    HighDimensionalLatticeKind.faceCenteredCubic3D.threshold =
      (0.65 : Real) := by
  norm_num [HighDimensionalLatticeKind.threshold]

@[simp] theorem highDimensionalThreshold_simpleCubic3D :
    HighDimensionalLatticeKind.simpleCubic3D.threshold = (0.95 : Real) := by
  norm_num [HighDimensionalLatticeKind.threshold]

/-- Boundary metadata for a supplied modal-energy source. -/
inductive HighDimensionalBoundaryConvention
  | fixed
  | periodic
  deriving DecidableEq

/-- A family-tagged energy source with an arbitrary finite mode type at each
size. -/
structure HighDimensionalModalEnergySource
    (kind : HighDimensionalLatticeKind) (Omega : Type) where
  boundary : HighDimensionalBoundaryConvention
  Mode : Nat -> Type
  modeFintype : forall side, Fintype (Mode side)
  /-- Positive linear size supplies at least one physical mode. -/
  modeNonempty : forall side, 0 < side -> Nonempty (Mode side)
  energy : forall side : Nat, Real -> Omega -> Real -> Mode side -> Real

instance {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega) (side : Nat) :
    Fintype (source.Mode side) :=
  source.modeFintype side

/-- Exact fixed-boundary tag for a paper-matched source.  This checks declared
metadata; it does not independently derive the supplied energy trajectory from
a fixed-boundary Hamiltonian. -/
def HighDimensionalModalEnergySource.IsPaperMatched
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega) : Prop :=
  source.boundary = .fixed

/-- The published all-mode normalized spectral-entropy indicator. -/
def highDimensionalAllModeXi {Mode : Type} [Fintype Mode]
    (energy : Mode -> Real) : Real :=
  normalizedEffectiveModeFraction (normalizedWeights energy)

/-- Formula lock for `xi = exp(zeta) / card`, with
`zeta = -sum w_k log w_k`. -/
theorem highDimensionalAllModeXi_eq_expEntropy_div_card
    {Mode : Type} [Fintype Mode] (energy : Mode -> Real) :
    highDimensionalAllModeXi energy =
      Real.exp (spectralEntropy (normalizedWeights energy)) /
        (Fintype.card Mode : Real) := by
  rfl

/-- Late-window all-mode indicator. -/
def highDimensionalLateWindowAllModeXi
    {Mode : Type} [Fintype Mode]
    (energy : Real -> Mode -> Real) (mu T : Real) : Real :=
  highDimensionalAllModeXi (lateWindowAverage energy mu T)

/-- Exact rescaling on nonnegative late-window endpoints. -/
theorem highDimensionalLateWindowAllModeXi_rescaling_nonnegative
    {Mode : Type} [Fintype Mode]
    (energyG energyOne : Real -> Mode -> Real)
    (mu g : Real) (hg : g ≠ 0) (hmu : 0 <= mu ∧ mu < 1)
    (hrescale : forall t i, energyG t i = energyOne (g ^ 2 * t) i)
    (hcontinuous : forall i, Continuous (fun tau => energyOne tau i)) :
    forall T, 0 <= T ->
      highDimensionalLateWindowAllModeXi energyG mu T =
        highDimensionalLateWindowAllModeXi energyOne mu (g ^ 2 * T) := by
  intro T hT
  rcases hT.eq_or_lt with rfl | hTpos
  · have hzero (energy : Real -> Mode -> Real) :
        lateWindowAverage energy mu 0 = 0 := by
      funext i
      simp [lateWindowAverage]
    simp only [mul_zero, highDimensionalLateWindowAllModeXi]
    rw [hzero energyG, hzero energyOne]
  · unfold highDimensionalLateWindowAllModeXi
    rw [ArchonPhysics.LateWindowRescaling.lateWindowAverage_rescaling_of_continuous
      energyG energyOne mu T g hg hmu.2 hTpos hrescale hcontinuous]

/-- Arbitrary finite mode type, arbitrary threshold, and no
dimension-dependent constant: exact `g^2` rescaling of the closed hit. -/
theorem highDimensionalAllModeXiThresholdHittingTime_kineticScale
    {Mode : Type} [Fintype Mode]
    (energyG energyOne : Real -> Mode -> Real)
    (threshold mu g : Real) (hg : g ≠ 0)
    (hmu : 0 <= mu ∧ mu < 1)
    (hrescale : forall t i, energyG t i = energyOne (g ^ 2 * t) i)
    (hcontinuous : forall i, Continuous (fun tau => energyOne tau i)) :
    ENNReal.ofReal (g ^ 2) *
        paperXiThresholdHittingTime
          (fun T => highDimensionalLateWindowAllModeXi energyG mu T)
          threshold =
      paperXiThresholdHittingTime
        (fun tau => highDimensionalLateWindowAllModeXi energyOne mu tau)
        threshold := by
  apply paperXiThresholdHittingTime_eq_of_kinetic_rescaling
  · exact hg
  · exact highDimensionalLateWindowAllModeXi_rescaling_nonnegative
      energyG energyOne mu g hg hmu hrescale hcontinuous

/-- Random all-mode diagnostic profile for a supplied family source. -/
def HighDimensionalModalEnergySource.xiProfile
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (mu : Real) (side : Nat) (g : Real) (omega : Omega) : Real -> Real :=
  fun T => highDimensionalLateWindowAllModeXi
    (source.energy side g omega) mu T

/-- Family-specific published-threshold equilibration time. -/
def HighDimensionalModalEnergySource.equilibrationTime
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (mu : Real) : Nat -> Real -> Omega -> ENNReal :=
  fun side g omega => paperXiThresholdHittingTime
    (source.xiProfile mu side g omega) kind.threshold

/-- Minimal, boundary-independent algebraic energy-density transfer.  It is
valid for any supplied all-mode hitting-time family satisfying the explicit
g^2 high-probability input.  In particular, it also applies to a periodic
source under that same input, but this alone is not a claim about the published
fixed-boundary experiment. -/
theorem highDimensionalFamilyXi_energyDensity_transfer
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {kind : HighDimensionalLatticeKind}
    (source : HighDimensionalModalEnergySource kind Omega)
    (mu : Real)
    (sizeCutoff : Real -> Nat) (lower upper : Real)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (lambda : Real) (n : Nat) (hn : 3 <= n) (hlambda : lambda ≠ 0)
    (s : AdmissibleJointLimit sizeCutoff)
    (epsilon : Nat -> Real) (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (EnergyDensityThermalization.energyDensityWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) := by
  exact EnergyDensityThermalization.HighProbabilityG2Bounds.energyDensity_corollary
    P (source.equilibrationTime mu) sizeCutoff lower upper h
      lambda n hn hlambda s epsilon hepsilon hcoupling

/-- Paper-matched fixed-boundary wrapper around the minimal algebraic
transfer.  The side and window assumptions record that the all-mode observable
is evaluated on a nonempty finite mode set and with a valid late window. -/
theorem highDimensionalFamilyXi_energyDensity_corollary
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {kind : HighDimensionalLatticeKind}
    (source : HighDimensionalModalEnergySource kind Omega)
    (_hfixed : source.IsPaperMatched)
    (mu : Real) (_hmu : 0 <= mu ∧ mu < 1)
    (sizeCutoff : Real -> Nat) (lower upper : Real)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (lambda : Real) (n : Nat) (hn : 3 <= n) (hlambda : lambda ≠ 0)
    (s : AdmissibleJointLimit sizeCutoff)
    (hside : forall j, 0 < s.systemSize j)
    (epsilon : Nat -> Real) (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (EnergyDensityThermalization.energyDensityWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) := by
  have _hmode : forall j, Nonempty (source.Mode (s.systemSize j)) :=
    fun j => source.modeNonempty _ (hside j)
  exact highDimensionalFamilyXi_energyDensity_transfer P source mu
    sizeCutoff lower upper h lambda n hn hlambda s epsilon hepsilon hcoupling

/-- Explicit cubic `lambda^-2 epsilon^-1` event. -/
def highDimensionalCubicWindowEvent {Omega : Type}
    (equilibrationTime : Nat -> Real -> Omega -> ENNReal)
    (lower upper : Real) (side : Nat) (lambda epsilon : Real) : Set Omega :=
  equilibrationTime side (effectiveCoupling lambda epsilon 3) ⁻¹'
    Icc
      (ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon ^ (-1 : Int)) *
        ENNReal.ofReal lower)
      (ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon ^ (-1 : Int)) *
        ENNReal.ofReal upper)

/-- Explicit quartic `lambda^-2 epsilon^-2` event. -/
def highDimensionalQuarticWindowEvent {Omega : Type}
    (equilibrationTime : Nat -> Real -> Omega -> ENNReal)
    (lower upper : Real) (side : Nat) (lambda epsilon : Real) : Set Omega :=
  equilibrationTime side (effectiveCoupling lambda epsilon 4) ⁻¹'
    Icc
      (ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon ^ (-2 : Int)) *
        ENNReal.ofReal lower)
      (ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon ^ (-2 : Int)) *
        ENNReal.ofReal upper)

theorem highDimensionalInverseSquareEnergyScale_cubic
    (lambda epsilon : Real) :
    EnergyDensityThermalization.inverseSquareEnergyScale lambda epsilon 3 =
      ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon ^ (-1 : Int)) := by
  norm_num [EnergyDensityThermalization.inverseSquareEnergyScale]

theorem highDimensionalInverseSquareEnergyScale_quartic
    (lambda epsilon : Real) :
    EnergyDensityThermalization.inverseSquareEnergyScale lambda epsilon 4 =
      ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon ^ (-2 : Int)) := by
  norm_num [EnergyDensityThermalization.inverseSquareEnergyScale]

/-- Cubic specialization.  In the numerical interpretation, n = 3
describes the cubic-leading low-energy scaling of the stable Lennard-Jones
interaction; it does not posit a standalone pure-cubic high-dimensional
Hamiltonian. -/
theorem highDimensionalFamilyXi_cubic_energyDensity_corollary
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {kind : HighDimensionalLatticeKind}
    (source : HighDimensionalModalEnergySource kind Omega)
    (hfixed : source.IsPaperMatched)
    (mu : Real) (hmu : 0 <= mu ∧ mu < 1)
    (sizeCutoff : Real -> Nat) (lower upper : Real)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (s : AdmissibleJointLimit sizeCutoff)
    (hside : forall j, 0 < s.systemSize j)
    (epsilon : Nat -> Real) (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 3) :
    Tendsto
      (fun j => P (highDimensionalCubicWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) := by
  have hgeneral := highDimensionalFamilyXi_energyDensity_corollary P
    source hfixed mu hmu sizeCutoff lower upper h lambda 3 (by norm_num)
      hlambda s hside epsilon hepsilon hcoupling
  simpa only [highDimensionalCubicWindowEvent,
    EnergyDensityThermalization.energyDensityWindowEvent,
    highDimensionalInverseSquareEnergyScale_cubic] using hgeneral

/-- Quartic specialization for any published family. -/
theorem highDimensionalFamilyXi_quartic_energyDensity_corollary
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {kind : HighDimensionalLatticeKind}
    (source : HighDimensionalModalEnergySource kind Omega)
    (hfixed : source.IsPaperMatched)
    (mu : Real) (hmu : 0 <= mu ∧ mu < 1)
    (sizeCutoff : Real -> Nat) (lower upper : Real)
    (h : HighProbabilityG2Bounds P (source.equilibrationTime mu)
      sizeCutoff lower upper)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (s : AdmissibleJointLimit sizeCutoff)
    (hside : forall j, 0 < s.systemSize j)
    (epsilon : Nat -> Real) (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 4) :
    Tendsto
      (fun j => P (highDimensionalQuarticWindowEvent
        (source.equilibrationTime mu) lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) := by
  have hgeneral := highDimensionalFamilyXi_energyDensity_corollary P
    source hfixed mu hmu sizeCutoff lower upper h lambda 4 (by norm_num)
      hlambda s hside epsilon hepsilon hcoupling
  simpa only [highDimensionalQuarticWindowEvent,
    EnergyDensityThermalization.energyDensityWindowEvent,
    highDimensionalInverseSquareEnergyScale_quartic] using hgeneral

end

end ArchonPhysics.DimensionalPaperSpectralEntropyScaling
