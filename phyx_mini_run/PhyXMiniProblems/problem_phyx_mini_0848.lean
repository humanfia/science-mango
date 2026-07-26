import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0848

open Dimension
open scoped BigOperators

/-!
# Net electric flux through a cylindrical Gaussian surface

The figure shows a closed cylindrical Gaussian surface and three point
charges.  The `+100 nC` charge is outside to the left, the `+1 nC` charge is
inside, and the `-100 nC` charge is outside to the right.  Consequently only
the central charge contributes to the enclosed charge in Gauss's law, even
though all three charges can contribute to the electric field on the surface.

Charge, vacuum permittivity, and electric flux are represented by Physlib
dimension-carrying quantities.  Real numbers below are only named readouts in
specified units or Cartesian-coordinate readouts in metres.
-/

/-! ## Dimensionful electromagnetic quantities and unit readouts -/

/-- The physical dimension of electric flux, `N m² / C`. -/
def electricFluxDimension : Dimension := ⟨3, -2, 1, -1, 0⟩

/-- The physical dimension of vacuum permittivity, `C² / (N m²) = F / m`. -/
def vacuumPermittivityDimension : Dimension := ⟨-3, 2, -1, 2, 0⟩

/-- A unit-independent physical electric charge. -/
abbrev ElectricCharge : Type := Dimensionful (WithDim C𝓭 ℝ)

/-- A unit-independent physical electric flux. -/
abbrev ElectricFlux : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- A unit-independent physical vacuum permittivity. -/
abbrev VacuumPermittivity : Type :=
  Dimensionful (WithDim vacuumPermittivityDimension ℝ)

/-- SI base units with the charge unit replaced by one nanocoulomb. -/
noncomputable def nanoCoulombUnitChoices : UnitChoices :=
  { UnitChoices.SI with
      charge := ChargeUnit.scale (1 / 1000000000) ChargeUnit.coulombs }

/-- Scalar readout of a physical charge in SI coulombs. -/
def chargeInCoulombs (charge : ElectricCharge) : ℝ :=
  (charge UnitChoices.SI).val

/-- Scalar readout of a physical charge in nanocoulombs. -/
def chargeInNanocoulombs (charge : ElectricCharge) : ℝ :=
  (charge nanoCoulombUnitChoices).val

/-- Scalar SI readout of electric flux in `N m² / C`. -/
def fluxInNewtonMetersSquaredPerCoulomb (flux : ElectricFlux) : ℝ :=
  (flux UnitChoices.SI).val

/-- Scalar SI readout of vacuum permittivity in `F / m`. -/
def permittivityInFaradsPerMeter (permittivity : VacuumPermittivity) : ℝ :=
  (permittivity UnitChoices.SI).val

/-! ## Closed-cylinder geometry and figure labels -/

/-- Cartesian position readouts in metres in the figure's ambient space. -/
abbrev Point3 := Fin 3 → ℝ

/-- The three boundary pieces of the closed cylindrical Gaussian surface. -/
inductive CylinderSurfacePart where
  | leftCap
  | curvedSide
  | rightCap
  deriving DecidableEq, Repr

/-!
A finite closed cylinder.  `axisDirection` is dimensionless, while the
centre, radius, and half-length are metre readouts.  Its boundary consists of
the two caps and curved side named by `CylinderSurfacePart`.
-/
structure CylindricalGaussianSurface where
  centerMeters : Point3
  axisDirection : Point3
  radiusMeters : ℝ
  halfLengthMeters : ℝ
  axis_is_unit : ∑ i : Fin 3, axisDirection i ^ 2 = 1
  radius_positive : 0 < radiusMeters
  halfLength_positive : 0 < halfLengthMeters

/-- Signed axial displacement of a point from the cylinder centre, in metres. -/
def CylindricalGaussianSurface.axialOffsetMeters
    (surface : CylindricalGaussianSurface) (point : Point3) : ℝ :=
  ∑ i : Fin 3,
    (point i - surface.centerMeters i) * surface.axisDirection i

/-- Squared radial distance from the cylinder axis, in square metres. -/
def CylindricalGaussianSurface.radialDistanceSquaredMeters
    (surface : CylindricalGaussianSurface) (point : Point3) : ℝ :=
  ∑ i : Fin 3,
    ((point i - surface.centerMeters i) -
      surface.axialOffsetMeters point * surface.axisDirection i) ^ 2

/-- Strict containment in the finite cylinder bounded by the Gaussian surface. -/
def CylindricalGaussianSurface.Contains
    (surface : CylindricalGaussianSurface) (point : Point3) : Prop :=
  |surface.axialOffsetMeters point| < surface.halfLengthMeters ∧
    surface.radialDistanceSquaredMeters point < surface.radiusMeters ^ 2

/-- Labels and left-to-right roles of the three point charges in the figure. -/
inductive ChargeLabel where
  | leftOutside
  | centralInside
  | rightOutside
  deriving DecidableEq, Fintype, Repr

/-- A point charge with a physical charge and a position readout in metres. -/
structure PointCharge where
  positionMeters : Point3
  charge : ElectricCharge

/-!
Physlib supplies the time-dependent electric-field type, but currently no
closed-surface electric-flux integral for this elementary geometry.  This
interface records precisely that missing physical operation: the net outward
flux of a field through the complete cylindrical boundary.
-/
structure ElectricFluxFunctional where
  netOutwardFlux :
    Electromagnetism.ElectricField → Time →
      CylindricalGaussianSurface → ElectricFlux

/-!
The electrostatic configuration represented by the question.  No numerical
flux or answer-choice value is stored in this setup.
-/
structure CylinderElectrostaticsSetup where
  cylinder : CylindricalGaussianSurface
  pointCharge : ChargeLabel → PointCharge
  electricField : Electromagnetism.ElectricField
  observationTime : Time
  vacuumPermittivity : VacuumPermittivity
  fluxFunctional : ElectricFluxFunctional

/-- The requested net outward electric flux through the cylinder. -/
def netCylinderFlux (setup : CylinderElectrostaticsSetup) : ElectricFlux :=
  setup.fluxFunctional.netOutwardFlux
    setup.electricField setup.observationTime setup.cylinder

/-!
Net charge strictly enclosed by the cylinder, read in coulombs.  External
charges contribute zero to this sum, exactly as required by Gauss's law.
-/
noncomputable def enclosedChargeInCoulombs
    (setup : CylinderElectrostaticsSetup) : ℝ := by
  classical
  exact ∑ label : ChargeLabel,
    if setup.cylinder.Contains (setup.pointCharge label).positionMeters then
      chargeInCoulombs (setup.pointCharge label).charge
    else
      0

/-! ## Figure/data readouts and governing law -/

/-!
Literal charge labels and inside/outside relations read from the supplied
figure.  These fields determine the enclosed charge but do not mention the
requested flux or any answer choice.
-/
structure MatchesCylinderChargeFigure
    (setup : CylinderElectrostaticsSetup) : Prop where
  left_charge_nanocoulombs :
    chargeInNanocoulombs (setup.pointCharge .leftOutside).charge = 100
  central_charge_nanocoulombs :
    chargeInNanocoulombs (setup.pointCharge .centralInside).charge = 1
  right_charge_nanocoulombs :
    chargeInNanocoulombs (setup.pointCharge .rightOutside).charge = -100
  left_charge_is_outside :
    ¬ setup.cylinder.Contains
      (setup.pointCharge .leftOutside).positionMeters
  central_charge_is_inside :
    setup.cylinder.Contains
      (setup.pointCharge .centralInside).positionMeters
  right_charge_is_outside :
    ¬ setup.cylinder.Contains
      (setup.pointCharge .rightOutside).positionMeters

/-!
The standard numerical calibration of vacuum permittivity used to evaluate
the multiple-choice answer.  The rational is the decimal
`8.8541878128 × 10⁻¹² F/m` written without floating-point notation.
-/
structure UsesStandardVacuumPermittivity
    (setup : CylinderElectrostaticsSetup) : Prop where
  vacuum_permittivity_si :
    permittivityInFaradsPerMeter setup.vacuumPermittivity =
      88541878128 / 10000000000000000000000

/-!
Integral Gauss law for this closed surface, written in division-free SI form:
`ε₀ Φ = Q_enclosed`.  It is a governing physical law, not the requested
numerical conclusion.
-/
structure SatisfiesIntegralGaussLaw
    (setup : CylinderElectrostaticsSetup) : Prop where
  vacuum_permittivity_positive :
    0 < permittivityInFaradsPerMeter setup.vacuumPermittivity
  gauss_law :
    permittivityInFaradsPerMeter setup.vacuumPermittivity *
        fluxInNewtonMetersSquaredPerCoulomb (netCylinderFlux setup) =
      enclosedChargeInCoulombs setup

/-! ## Derived relations and answer target -/

/-!
Only the central `+1 nC` point charge lies inside the Gaussian cylinder, so
the net enclosed charge is `10⁻⁹ C`.  The two exterior `100 nC` charges do not
enter the enclosed-charge sum.
-/
lemma enclosedChargeInCoulombs_eq_one_nanocoulomb
    (setup : CylinderElectrostaticsSetup)
    (_figure : MatchesCylinderChargeFigure setup) :
    enclosedChargeInCoulombs setup = 1 / 1000000000 := by
  have charge_conversion (charge : ElectricCharge) :
      chargeInCoulombs charge =
        chargeInNanocoulombs charge / 1000000000 := by
    have hscale :
        UnitChoices.SI.dimScale nanoCoulombUnitChoices C𝓭 =
          (1000000000 : NNReal) := by
      apply NNReal.eq
      norm_num [nanoCoulombUnitChoices, UnitChoices.dimScale_apply,
        ChargeUnit.scale, ChargeUnit.coulombs, ChargeUnit.div_eq_val, C𝓭]
      rfl
    have h := congrArg WithDim.val
      (charge.property UnitChoices.SI nanoCoulombUnitChoices)
    simp only [WithDim.smul_val, WithDim.dim_apply] at h
    rw [hscale] at h
    norm_num [chargeInCoulombs, chargeInNanocoulombs, NNReal.smul_def] at h ⊢
    linarith
  classical
  rw [enclosedChargeInCoulombs]
  rw [show (Finset.univ : Finset ChargeLabel) =
    {.leftOutside, .centralInside, .rightOutside} by decide]
  simp [_figure.left_charge_is_outside,
    _figure.central_charge_is_inside,
    _figure.right_charge_is_outside, charge_conversion,
    _figure.central_charge_nanocoulombs]

/-! Gauss's law gives flux as enclosed charge divided by vacuum permittivity. -/
lemma netCylinderFlux_eq_enclosedCharge_div_permittivity
    (setup : CylinderElectrostaticsSetup)
    (_law : SatisfiesIntegralGaussLaw setup) :
    fluxInNewtonMetersSquaredPerCoulomb (netCylinderFlux setup) =
      enclosedChargeInCoulombs setup /
        permittivityInFaradsPerMeter setup.vacuumPermittivity := by
  apply (eq_div_iff (ne_of_gt _law.vacuum_permittivity_positive)).2
  simpa [mul_comm] using _law.gauss_law

/-- Labels of the four displayed flux choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Flux readout printed beside each answer choice, in `N m² / C`. -/
def AnswerChoice.fluxInNewtonMetersSquaredPerCoulomb : AnswerChoice → ℝ
  | .A => 120
  | .B => -100
  | .C => 200
  | .D => 110

/-!
A displayed choice is correct when its printed value is at least as close to
the computed physical flux as every other displayed value.
-/
def IsNearestDisplayedFluxChoice
    (setup : CylinderElectrostaticsSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |fluxInNewtonMetersSquaredPerCoulomb (netCylinderFlux setup) -
        choice.fluxInNewtonMetersSquaredPerCoulomb| ≤
      |fluxInNewtonMetersSquaredPerCoulomb (netCylinderFlux setup) -
        other.fluxInNewtonMetersSquaredPerCoulomb|

/-!
The enclosed charge and vacuum-permittivity calibration give the exact model
readout `10¹³ / 88541878128 ≈ 112.94 N m²/C`.  Among the displayed values this
is nearest to `110 N m²/C`, answer choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0848:target`.
-/
theorem problem_phyx_mini_0848
    (setup : CylinderElectrostaticsSetup)
    (_figure : MatchesCylinderChargeFigure setup)
    (_permittivity : UsesStandardVacuumPermittivity setup)
    (_gaussLaw : SatisfiesIntegralGaussLaw setup) :
    fluxInNewtonMetersSquaredPerCoulomb (netCylinderFlux setup) =
        10000000000000 / 88541878128 ∧
      IsNearestDisplayedFluxChoice setup .D := by
  have hFlux :=
    netCylinderFlux_eq_enclosedCharge_div_permittivity setup _gaussLaw
  rw [enclosedChargeInCoulombs_eq_one_nanocoulomb setup _figure,
    _permittivity.vacuum_permittivity_si] at hFlux
  constructor
  · calc
      fluxInNewtonMetersSquaredPerCoulomb (netCylinderFlux setup) =
          (1 / 1000000000 : ℝ) /
            (88541878128 / 10000000000000000000000) := hFlux
      _ = 10000000000000 / 88541878128 := by norm_num
  · unfold IsNearestDisplayedFluxChoice
    intro other
    rw [hFlux]
    fin_cases other <;>
      norm_num [AnswerChoice.fluxInNewtonMetersSquaredPerCoulomb,
        abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0848
