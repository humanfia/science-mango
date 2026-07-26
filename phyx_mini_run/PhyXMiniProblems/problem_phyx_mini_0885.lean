import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0885

open Dimension

/-!
# Inductance per unit length of a coaxial cable

A high-frequency signal travels on the cylindrical inner conductor of a
coaxial cable. The surrounding conductor is grounded, and insulating material
fills the annular region between the conductors. The problem gives radii
`r₁ = 0.50 mm` and `r₂ = 3.0 mm` and asks for the inductance per metre.

Lengths, magnetic permeability, and inductance per unit length are represented
by unit-independent Physlib quantities. Real numbers occur only at explicit
unit-readout boundaries, in literal figure/question data, and in displayed
answer choices. The numerical answer is a rounded value: the ideal coaxial law
gives approximately `0.3584 μH/m`, displayed as `0.36 μH/m`.

Assumption/target split:

* governing law: the general high-frequency coaxial relation
  `L' = μ/(2π) log (r₂/r₁)`, with the nonmagnetic fill calibrated to
  vacuum permeability;
* previous-part results: none;
* figure/data readouts: the concentric cylindrical conductors, common axis,
  arrows labelled `r₁` and `r₂`, grounded outer conductor, insulating fill
  and coating, and radius readings `0.50 mm` and `3.0 mm`;
* current target: the inductance rounds to `0.36 μH/m` and uniquely selects
  recorded answer C.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- The physical dimension `M L² C⁻²` of electrical inductance. -/
def inductanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M L C⁻²` of inductance per length. -/
def inductancePerLengthDimension : Dimension :=
  inductanceDimension * L𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent inductance per unit length. -/
abbrev InductancePerLengthQuantity : Type :=
  Dimensionful (WithDim inductancePerLengthDimension NNReal)

/-!
Magnetic permeability and inductance per length have the same physical
dimension (`H/m`). They remain distinct through their physical roles and
separate readout functions.
-/
/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim inductancePerLengthDimension NNReal)

/-- Read a physical length using the length unit selected by `units`. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read a physical length in millimetres. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout { UnitChoices.SI with length := LengthUnit.millimeters } length

/-- Read an inductance per length in the coherent unit induced by `units`. -/
def inductancePerLengthReadout
    (units : UnitChoices) (inductancePerLength : InductancePerLengthQuantity) : ℝ :=
  ((inductancePerLength units).val : ℝ)

/-- Read an inductance per length in coherent-SI henries per metre. -/
def inductancePerLengthInHenriesPerMeter
    (inductancePerLength : InductancePerLengthQuantity) : ℝ :=
  inductancePerLengthReadout UnitChoices.SI inductancePerLength

/-- Read an inductance per length in microhenries per metre. -/
def inductancePerLengthInMicrohenriesPerMeter
    (inductancePerLength : InductancePerLengthQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * inductancePerLengthInHenriesPerMeter inductancePerLength

/-- Read magnetic permeability in the coherent unit induced by `units`. -/
def magneticPermeabilityReadout
    (units : UnitChoices) (permeability : MagneticPermeabilityQuantity) : ℝ :=
  ((permeability units).val : ℝ)

/-- Read magnetic permeability in coherent-SI henries per metre. -/
def magneticPermeabilityInHenriesPerMeter
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  magneticPermeabilityReadout UnitChoices.SI permeability

/-! ## Cable roles and primary-figure vocabulary -/

/-- The two cylindrical conductors identified in the scenario and image. -/
inductive CableConductor where
  | inner
  | outer
  deriving DecidableEq, Fintype, Repr

/-- The electromagnetic idealization assigned to a conductor. -/
inductive ConductorModel where
  | highFrequencyIdealConductor
  | other
  deriving DecidableEq, Repr

/-- The two insulating material roles described in the written scenario. -/
inductive InsulatingMaterialModel where
  | softFlexibleFill
  | plasticOuterCoating
  | other
  deriving DecidableEq, Repr

/-- Magnetic behavior of the dielectric fill used by the textbook formula. -/
inductive MagneticMaterialModel where
  | nonmagnetic
  | other
  deriving DecidableEq, Repr

/-- Frequency regimes distinguished by the cable model. -/
inductive SignalFrequencyRegime where
  | highFrequency
  | other
  deriving DecidableEq, Repr

/-- Text or symbolic annotations visible in the supplied cable image. -/
inductive FigureLabel where
  | innerConductorRadiusR1
  | radiusR2
  | outerConductor
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation features of image `885.png`. These fields describe the
two concentric cylinders, dashed common axis, and the arrows labelled `r₁`
and `r₂`; they contain no inductance value.
-/
structure CoaxialCableFigure where
  conductorShown : CableConductor → Bool
  labelShown : FigureLabel → Bool
  cylindricalPerspectiveShown : Bool
  commonAxisShownDashed : Bool
  circularCrossSectionsAreConcentric : Bool
  outerConductorSurroundsInner : Bool
  r1ArrowRunsFromAxisToInnerSurface : Bool
  r2ArrowRunsFromAxisToOuterRadius : Bool

/-!
Independent physical data for the cable. The requested inductance per length
is an unconstrained physical quantity here; only the governing law below
relates it to the radii and permeability.
-/
structure CoaxialCableSetup where
  conductorModel : CableConductor → ConductorModel
  signalRegime : SignalFrequencyRegime
  signalCarriedBy : CableConductor
  outerConductorGrounded : Bool
  interconductorFill : InsulatingMaterialModel
  outerCoating : InsulatingMaterialModel
  fillMagneticModel : MagneticMaterialModel
  innerRadiusR1 : LengthQuantity
  outerRadiusR2 : LengthQuantity
  fillMagneticPermeability : MagneticPermeabilityQuantity
  inductancePerLength : InductancePerLengthQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  figure : CoaxialCableFigure

/-! ## Scenario assumptions, readouts, and governing law -/

/-- The qualitative cable model stated in the written problem. -/
structure MatchesWrittenCoaxialCableScenario
    (setup : CoaxialCableSetup) : Prop where
  signalIsHighFrequency : setup.signalRegime = .highFrequency
  innerConductorCarriesSignal : setup.signalCarriedBy = .inner
  surroundingConductorIsGrounded : setup.outerConductorGrounded = true
  bothConductorsUseHighFrequencyModel : ∀ conductor,
    setup.conductorModel conductor = .highFrequencyIdealConductor
  annularFillIsSoftFlexibleInsulator :
    setup.interconductorFill = .softFlexibleFill
  exteriorCoatingIsInsulatingPlastic :
    setup.outerCoating = .plasticOuterCoating
  fillIsNonmagnetic : setup.fillMagneticModel = .nonmagnetic

/-!
Primary-raster evidence. It records the labelled coaxial geometry only; the
radius calibrations come from the question text and are stated separately.
-/
structure MatchesSuppliedCoaxialCableFigure
    (setup : CoaxialCableSetup) : Prop where
  bothConductorsShown : ∀ conductor,
    setup.figure.conductorShown conductor = true
  allPrintedLabelsShown : ∀ label,
    setup.figure.labelShown label = true
  cableIsDrawnCylindrically : setup.figure.cylindricalPerspectiveShown = true
  dashedCommonAxisIsShown : setup.figure.commonAxisShownDashed = true
  crossSectionsAreConcentric :
    setup.figure.circularCrossSectionsAreConcentric = true
  outerSurroundsInner : setup.figure.outerConductorSurroundsInner = true
  r1ArrowHasDepictedEndpoints :
    setup.figure.r1ArrowRunsFromAxisToInnerSurface = true
  r2ArrowHasDepictedEndpoints :
    setup.figure.r2ArrowRunsFromAxisToOuterRadius = true

/-!
The two numerical radius readouts supplied in the question. They constrain
only the cable geometry and contain no inductance value.
-/
structure MatchesProblemRadiusReadouts
    (setup : CoaxialCableSetup) : Prop where
  innerRadiusIsPointFiveMillimeters :
    lengthInMillimeters setup.innerRadiusR1 = 0.50
  outerRadiusIsThreeMillimeters :
    lengthInMillimeters setup.outerRadiusR2 = 3.0

/-- Positivity and nesting required by the logarithmic coaxial formula. -/
structure HasPhysicalCoaxialParameters
    (setup : CoaxialCableSetup) : Prop where
  innerRadiusPositive :
    0 < lengthReadout UnitChoices.SI setup.innerRadiusR1
  innerRadiusLessThanOuterRadius :
    lengthReadout UnitChoices.SI setup.innerRadiusR1 <
      lengthReadout UnitChoices.SI setup.outerRadiusR2
  magneticPermeabilityPositive :
    0 < magneticPermeabilityInHenriesPerMeter
      setup.fillMagneticPermeability

/-!
The nonmagnetic fill has the permeability of free space. Physlib's
`Electromagnetism.EMSystem.μ₀` supplies the electromagnetic-system parameter;
the second field gives the coherent-SI calibration
`μ₀ = 4π × 10⁻⁷ H/m`. Neither field mentions the requested inductance.
-/
structure UsesTextbookVacuumMagneticPermeability
    (setup : CoaxialCableSetup) : Prop where
  fillPermeabilityAgreesWithElectromagneticSystem :
    magneticPermeabilityInHenriesPerMeter
        setup.fillMagneticPermeability =
      setup.electromagneticSystem.μ₀
  textbookVacuumPermeabilityCalibration :
    setup.electromagneticSystem.μ₀ =
      4 * Real.pi / (10 : ℝ) ^ 7

/-!
The general governing high-frequency coaxial-cable law

`L' = μ / (2π) * log (r₂ / r₁)`.

It is stated in every coherent unit system. The radius ratio is dimensionless,
and magnetic permeability and inductance per length have the same dimension.
This law contains no answer choice or rounded target value.
-/
structure SatisfiesHighFrequencyCoaxialInductanceLaw
    (setup : CoaxialCableSetup) : Prop where
  coaxialInductanceLaw : ∀ units : UnitChoices,
    inductancePerLengthReadout units setup.inductancePerLength =
      magneticPermeabilityReadout units setup.fillMagneticPermeability /
          (2 * Real.pi) *
        Real.log
          (lengthReadout units setup.outerRadiusR2 /
            lengthReadout units setup.innerRadiusR1)

/-! ## Rounded numerical result and displayed answer choices -/

/-- The four answer labels shown with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed numerical readout for each choice, in `μH/m`. -/
def AnswerChoice.displayedInductanceInMicrohenriesPerMeter :
    AnswerChoice → ℝ
  | .A => 0.24
  | .B => 0.48
  | .C => 0.36
  | .D => 0.30

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
`displayed` is the nearest-hundredth presentation of `actual` when their
difference is strictly less than half of one hundredth.
-/
def IsRoundedToDisplayedHundredth (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-- A choice agrees with the cable's computed inductance after rounding. -/
def AnswerMatchesRoundedInductance
    (setup : CoaxialCableSetup) (choice : AnswerChoice) : Prop :=
  IsRoundedToDisplayedHundredth
    (inductancePerLengthInMicrohenriesPerMeter setup.inductancePerLength)
    choice.displayedInductanceInMicrohenriesPerMeter

/-!
**Blueprint target** `thm:physics:phyx_mini_0885:target`.

For `r₁ = 0.50 mm`, `r₂ = 3.0 mm`, and the textbook value of `μ₀`, the
coaxial law gives about `0.3584 μH/m`. Hence its two-decimal display is
`0.36 μH/m`, the recorded choice C, and no other displayed choice matches.

The target value and choice occur only on the conclusion/data side. They do
not occur in the setup, scenario, radius readouts, physical-parameter
conditions, permeability calibration, or governing-law predicate.
-/
theorem problem_phyx_mini_0885
    (setup : CoaxialCableSetup)
    (_hScenario : MatchesWrittenCoaxialCableScenario setup)
    (_hFigure : MatchesSuppliedCoaxialCableFigure setup)
    (_hRadii : MatchesProblemRadiusReadouts setup)
    (_hPhysical : HasPhysicalCoaxialParameters setup)
    (_hPermeability : UsesTextbookVacuumMagneticPermeability setup)
    (_hInductanceLaw : SatisfiesHighFrequencyCoaxialInductanceLaw setup) :
    IsRoundedToDisplayedHundredth
        (inductancePerLengthInMicrohenriesPerMeter setup.inductancePerLength)
        0.36 ∧
      AnswerMatchesRoundedInductance setup recordedDatasetAnswer ∧
      ∀ choice : AnswerChoice,
        AnswerMatchesRoundedInductance setup choice ↔ choice = .C := by
  have hInnerScale := congrArg
    (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
    (setup.innerRadiusR1.property UnitChoices.SI
      { UnitChoices.SI with length := LengthUnit.millimeters })
  have hOuterScale := congrArg
    (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
    (setup.outerRadiusR2.property UnitChoices.SI
      { UnitChoices.SI with length := LengthUnit.millimeters })
  have hInnerMillimeters :
      ((setup.innerRadiusR1
        { UnitChoices.SI with length := LengthUnit.millimeters }).val : ℝ) = 1 / 2 := by
    have h := _hRadii.innerRadiusIsPointFiveMillimeters
    change ((setup.innerRadiusR1
      { UnitChoices.SI with length := LengthUnit.millimeters }).val : ℝ) = 0.50 at h
    norm_num at h ⊢
    exact h
  have hOuterMillimeters :
      ((setup.outerRadiusR2
        { UnitChoices.SI with length := LengthUnit.millimeters }).val : ℝ) = 3 := by
    have h := _hRadii.outerRadiusIsThreeMillimeters
    change ((setup.outerRadiusR2
      { UnitChoices.SI with length := LengthUnit.millimeters }).val : ℝ) = 3.0 at h
    norm_num at h ⊢
    exact h
  have hRadiusRatio :
      lengthReadout UnitChoices.SI setup.outerRadiusR2 /
        lengthReadout UnitChoices.SI setup.innerRadiusR1 = 6 := by
    change ((setup.innerRadiusR1
      { UnitChoices.SI with length := LengthUnit.millimeters }).val : ℝ) =
        (UnitChoices.SI.dimScale
          { UnitChoices.SI with length := LengthUnit.millimeters } L𝓭 : ℝ) *
          ((setup.innerRadiusR1 UnitChoices.SI).val : ℝ) at hInnerScale
    change ((setup.outerRadiusR2
      { UnitChoices.SI with length := LengthUnit.millimeters }).val : ℝ) =
        (UnitChoices.SI.dimScale
          { UnitChoices.SI with length := LengthUnit.millimeters } L𝓭 : ℝ) *
          ((setup.outerRadiusR2 UnitChoices.SI).val : ℝ) at hOuterScale
    rw [hInnerScale] at hInnerMillimeters
    rw [hOuterScale] at hOuterMillimeters
    have hScalePos :
        0 < (UnitChoices.SI.dimScale
          { UnitChoices.SI with length := LengthUnit.millimeters } L𝓭 : ℝ) := by
      exact_mod_cast UnitChoices.dimScale_pos UnitChoices.SI
        { UnitChoices.SI with length := LengthUnit.millimeters } L𝓭
    have hInnerSIPos :
        0 < ((setup.innerRadiusR1 UnitChoices.SI).val : ℝ) := by
      exact _hPhysical.innerRadiusPositive
    dsimp [lengthReadout]
    apply (div_eq_iff (ne_of_gt hInnerSIPos)).2
    nlinarith [hInnerMillimeters, hOuterMillimeters]
  have hInductance :
      inductancePerLengthInMicrohenriesPerMeter setup.inductancePerLength =
        (1 / 5 : ℝ) * Real.log 6 := by
    have hPermeabilitySI :
        magneticPermeabilityReadout UnitChoices.SI setup.fillMagneticPermeability =
          4 * Real.pi / (10 : ℝ) ^ 7 := by
      simpa [magneticPermeabilityInHenriesPerMeter] using
        _hPermeability.fillPermeabilityAgreesWithElectromagneticSystem.trans
          _hPermeability.textbookVacuumPermeabilityCalibration
    rw [inductancePerLengthInMicrohenriesPerMeter,
      inductancePerLengthInHenriesPerMeter,
      _hInductanceLaw.coaxialInductanceLaw UnitChoices.SI,
      hPermeabilitySI, hRadiusRatio]
    field_simp [Real.pi_ne_zero]
    all_goals ring
  have hLogLower : (1.7917594688 : ℝ) < Real.log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hLogUpper : Real.log 6 < (1.7917594696 : ℝ) := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hRounded :
      IsRoundedToDisplayedHundredth
        (inductancePerLengthInMicrohenriesPerMeter setup.inductancePerLength) 0.36 := by
    rw [hInductance]
    rw [IsRoundedToDisplayedHundredth, abs_lt]
    constructor <;> norm_num at * <;> linarith
  refine ⟨hRounded, ?_, ?_⟩
  · simpa [AnswerMatchesRoundedInductance, recordedDatasetAnswer,
      AnswerChoice.displayedInductanceInMicrohenriesPerMeter] using hRounded
  · intro choice
    constructor
    · intro hChoice
      cases choice <;>
        simp_all [AnswerMatchesRoundedInductance, IsRoundedToDisplayedHundredth,
          AnswerChoice.displayedInductanceInMicrohenriesPerMeter, abs_lt] <;>
        linarith
    · intro hChoice
      subst choice
      simpa [AnswerMatchesRoundedInductance,
        AnswerChoice.displayedInductanceInMicrohenriesPerMeter] using hRounded

end PhyXMiniProblems.ProblemPhyXMini0885
