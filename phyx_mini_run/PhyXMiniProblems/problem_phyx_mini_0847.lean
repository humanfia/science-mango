import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0847

open Dimension

/-!
# Electric flux through a toroidal Gaussian surface

The supplied figure shows a toroidal closed surface. The charge marked
`-1 nC (inside)` lies in the solid-torus region enclosed by the surface,
whereas the charge marked `+100 nC` lies in the central hole of the torus.
Consequently, the latter charge is outside the volume bounded by the
toroidal surface even though it is visually surrounded by the torus.

Charges, vacuum permittivity, lengths, and electric flux are represented by
unit-independent Physlib quantities. Real numbers occur only as readouts in
named SI units or as the numerical labels printed in the source. In
particular, the net flux is an independent physical field constrained by
Gauss's law; it is not defined to be any answer choice.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A signed, unit-independent electric charge. -/
abbrev ChargeQuantity : Type := Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-!
Vacuum permittivity has SI dimension
`charge^2 * time^2 / (mass * length^3)`.
-/
def vacuumPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative, unit-independent vacuum permittivity. -/
abbrev VacuumPermittivityQuantity : Type :=
  Dimensionful (WithDim vacuumPermittivityDimension NNReal)

/-!
Electric flux has SI dimension
`force * length^2 / charge = mass * length^3 / (time^2 * charge)`.
-/
def electricFluxDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent electric flux. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coulomb readout of a signed electric charge. -/
def chargeInCoulombs (charge : ChargeQuantity) : ℝ :=
  signedSIReadout charge

/-- Nanocoulomb readout used by both charge labels in the figure. -/
def chargeInNanocoulombs (charge : ChargeQuantity) : ℝ :=
  1000000000 * chargeInCoulombs charge

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- SI readout of vacuum permittivity in `C^2 / (N m^2)`. -/
def vacuumPermittivityInSI
    (permittivity : VacuumPermittivityQuantity) : ℝ :=
  nonnegativeSIReadout permittivity

/-- Read electric flux in `N m^2 / C`. -/
def electricFluxInNewtonMetersSquaredPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  signedSIReadout flux

/-! ## Toroidal geometry and figure vocabulary -/

/-- The two point charges distinguished by the labels in the image. -/
inductive FigureCharge where
  | negativeOneNanocoulomb
  | positiveHundredNanocoulombs
  deriving DecidableEq, Fintype, Repr

/-- The sign symbol drawn inside a charge marker. -/
inductive ChargeSignMark where
  | plus
  | minus
  deriving DecidableEq, Repr

/-!
Regions relative to a toroidal Gaussian surface. Only `solidInterior` is
inside the volume bounded by the surface. The central hole belongs to the
complement of that volume.
-/
inductive TorusRelativeRegion where
  | solidInterior
  | centralHole
  | exterior
  deriving DecidableEq, Repr

/-- The indicator used when summing charge enclosed by a toroidal surface. -/
def torusEnclosureWeight : TorusRelativeRegion → ℝ
  | .solidInterior => 1
  | .centralHole => 0
  | .exterior => 0

/-!
The major and tube radii preserve the toroidal geometric role even though the
source supplies no calibrated length scale.
-/
structure TorusGaussianSurface where
  majorRadius : LengthQuantity
  tubeRadius : LengthQuantity

/-! Qualitative and numerical data read from the primary image. -/
structure TorusChargeFigure where
  regionOf : FigureCharge → TorusRelativeRegion
  signMarkOf : FigureCharge → ChargeSignMark
  printedChargeInNanocoulombs : FigureCharge → ℝ
  closedToroidalSurfaceShown : Bool
  hasCalibratedRadiusScale : Bool

/-!
The independent physical quantities in the electrostatic setup. In
particular, `netEnclosedCharge` and `netElectricFlux` remain independent until
the governing laws below relate them to the individual charges.
-/
structure TorusElectrostaticsSetup where
  torus : TorusGaussianSurface
  charge : FigureCharge → ChargeQuantity
  vacuumPermittivity : VacuumPermittivityQuantity
  netEnclosedCharge : ChargeQuantity
  netElectricFlux : ElectricFluxQuantity
  figure : TorusChargeFigure

/-! ## Assumptions: geometry, figure readouts, and governing laws -/

/-- Positivity and non-self-intersection conditions for the toroidal model. -/
structure HasPhysicalTorusParameters
    (setup : TorusElectrostaticsSetup) : Prop where
  positiveTubeRadius : 0 < lengthInMeters setup.torus.tubeRadius
  tubeRadiusLessThanMajorRadius :
    lengthInMeters setup.torus.tubeRadius <
      lengthInMeters setup.torus.majorRadius
  positiveVacuumPermittivity :
    0 < vacuumPermittivityInSI setup.vacuumPermittivity

/-!
Facts read from the supplied bitmap. The `+100 nC` charge is in the central
hole, not in the solid-torus interior; this topological distinction is the
essential figure-derived datum.
-/
structure MatchesSuppliedTorusFigure
    (setup : TorusElectrostaticsSetup) : Prop where
  toroidalSurfaceShown : setup.figure.closedToroidalSurfaceShown = true
  noCalibratedRadiusScale : setup.figure.hasCalibratedRadiusScale = false
  negativeChargeHasMinusMark :
    setup.figure.signMarkOf .negativeOneNanocoulomb = .minus
  positiveChargeHasPlusMark :
    setup.figure.signMarkOf .positiveHundredNanocoulombs = .plus
  negativeChargeLabel :
    setup.figure.printedChargeInNanocoulombs .negativeOneNanocoulomb = -1
  positiveChargeLabel :
    setup.figure.printedChargeInNanocoulombs .positiveHundredNanocoulombs = 100
  chargeReadoutAgreesWithPrintedLabel : ∀ chargeId,
    chargeInNanocoulombs (setup.charge chargeId) =
      setup.figure.printedChargeInNanocoulombs chargeId
  negativeChargeInsideSolidTorus :
    setup.figure.regionOf .negativeOneNanocoulomb = .solidInterior
  positiveChargeInCentralHole :
    setup.figure.regionOf .positiveHundredNanocoulombs = .centralHole

/-!
The textbook vacuum-permittivity calibration
`ε₀ = 8.85 × 10⁻¹² C²/(N m²)` used for the numerical estimate.
-/
structure UsesTextbookVacuumPermittivity
    (setup : TorusElectrostaticsSetup) : Prop where
  valueInSI :
    vacuumPermittivityInSI setup.vacuumPermittivity =
      885 / 100000000000000

/-!
The governing laws are charge accounting over the bounded solid-torus region
and integral Gauss's law `Φ_E = Q_enclosed / ε₀`. They are stated for the
general setup and contain neither the requested numerical flux nor an answer
choice.
-/
structure SatisfiesTorusGaussLaw
    (setup : TorusElectrostaticsSetup) : Prop where
  enclosedChargeAccounting :
    chargeInCoulombs setup.netEnclosedCharge =
      ∑ chargeId : FigureCharge,
        torusEnclosureWeight (setup.figure.regionOf chargeId) *
          chargeInCoulombs (setup.charge chargeId)
  integralGaussLaw :
    electricFluxInNewtonMetersSquaredPerCoulomb setup.netElectricFlux =
      chargeInCoulombs setup.netEnclosedCharge /
        vacuumPermittivityInSI setup.vacuumPermittivity

/-! ## Displayed answer choices and current targets -/

/-- Labels attached to the four displayed flux values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical value printed for an answer choice, in `N m^2 / C`. -/
def displayedFluxValue : AnswerChoice → ℝ
  | .A => 120
  | .B => -100
  | .C => 200
  | .D => -110

/-!
A choice is uniquely closest to the physical flux when its absolute error is
strictly smaller than that of every other displayed value. This definition
does not privilege any particular label.
-/
def IsUniqueClosestAnswerChoice
    (setup : TorusElectrostaticsSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |electricFluxInNewtonMetersSquaredPerCoulomb setup.netElectricFlux -
        displayedFluxValue choice| <
      |electricFluxInNewtonMetersSquaredPerCoulomb setup.netElectricFlux -
        displayedFluxValue other|

/-- The supplied figure and charge-accounting law give `Q_enclosed = -1 nC`. -/
theorem enclosed_charge_of_supplied_torus_figure
    (setup : TorusElectrostaticsSetup)
    (_figure : MatchesSuppliedTorusFigure setup)
    (_gauss : SatisfiesTorusGaussLaw setup) :
    chargeInNanocoulombs setup.netEnclosedCharge = -1 := by
  have hnegative :=
    (_figure.chargeReadoutAgreesWithPrintedLabel .negativeOneNanocoulomb).trans
      _figure.negativeChargeLabel
  rw [chargeInNanocoulombs, _gauss.enclosedChargeAccounting]
  rw [Finset.sum_eq_single .negativeOneNanocoulomb]
  · simpa [chargeInNanocoulombs, _figure.negativeChargeInsideSolidTorus,
      torusEnclosureWeight] using hnegative
  · intro b _ hb
    cases b with
    | negativeOneNanocoulomb => exact (hb rfl).elim
    | positiveHundredNanocoulombs =>
        simp [_figure.positiveChargeInCentralHole, torusEnclosureWeight]
  · simp

/-!
With the textbook value of `ε₀`, Gauss's law gives the exact model readout
`-20000/177 ≈ -112.994 N m²/C`. This is within `3 N m²/C` of the displayed
rounded value `-110 N m²/C`, and choice D is uniquely closest.

This is the formalization of blueprint label
`thm:physics:phyx_mini_0847:target`.
-/
theorem problem_phyx_mini_0847
    (setup : TorusElectrostaticsSetup)
    (_parameters : HasPhysicalTorusParameters setup)
    (_figure : MatchesSuppliedTorusFigure setup)
    (_vacuum : UsesTextbookVacuumPermittivity setup)
    (_gauss : SatisfiesTorusGaussLaw setup) :
    electricFluxInNewtonMetersSquaredPerCoulomb setup.netElectricFlux =
        -(20000 / 177 : ℝ) ∧
      |electricFluxInNewtonMetersSquaredPerCoulomb setup.netElectricFlux -
          displayedFluxValue .D| < 3 ∧
      IsUniqueClosestAnswerChoice setup .D := by
  have hcharge :=
    enclosed_charge_of_supplied_torus_figure setup _figure _gauss
  rw [chargeInNanocoulombs] at hcharge
  have hflux :
      electricFluxInNewtonMetersSquaredPerCoulomb setup.netElectricFlux =
        -(20000 / 177 : ℝ) := by
    rw [_gauss.integralGaussLaw, _vacuum.valueInSI]
    norm_num at hcharge ⊢
    linarith
  refine ⟨hflux, ?_, ?_⟩
  · rw [hflux]
    norm_num [displayedFluxValue, abs_of_nonpos, abs_of_nonneg]
  · intro other hother
    rw [hflux]
    cases other with
    | A => norm_num [displayedFluxValue, abs_of_nonpos, abs_of_nonneg]
    | B => norm_num [displayedFluxValue, abs_of_nonpos, abs_of_nonneg]
    | C => norm_num [displayedFluxValue, abs_of_nonpos, abs_of_nonneg]
    | D => exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0847
