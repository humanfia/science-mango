import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Area

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0940

open Dimension

/-!
# Self-inductance of a closely wound toroidal solenoid

The supplied figure shows a purple winding around a beige toroidal,
nonmagnetic core.  It labels the turn count `N`, cross-sectional area `A`,
mean radius `r`, and winding current `i`; dashed arrows indicate the magnetic
field around the toroid.  The written model assumes that the field magnitude
is uniform over each cross section.

Physical magnitudes are represented by Physlib's unit-independent
`Dimensionful (WithDim ...)` types.  Real numbers occur only at explicit
unit-readout boundaries, in turn counts, and in displayed answer choices.

Assumption/target split:

* governing laws: Ampere's circuital law around the mean toroidal path,
  uniform-cross-section flux `Φ = B A`, and the self-inductance flux-linkage
  relation `L I = N Φ`;
* previous-part results: none;
* figure/data readouts: the toroidal core and winding, purple current arrows,
  dashed field arrows, labels `N`, `A`, `r`, and `i`, and the note that only a
  few turns are drawn;
* current target: `L = μ₀ N² A / (2 π r)` in coherent SI units.

The self-inductance is an independent field of the setup.  It is not defined
from the requested formula or from the recorded `40 μH` answer choice.
-/

/-! ## Dimensionful electromagnetic quantities and coherent readouts -/

/-- Electric current has physical dimension charge per time, `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic permeability has SI dimension `M L C⁻²` (henries per metre). -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density has SI dimension `M T⁻¹ C⁻¹` (teslas). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux has dimension flux density times area (webers). -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * L𝓭 * L𝓭

/-- Self-inductance is magnetic flux divided by electric current (henries). -/
def inductanceDimension : Dimension :=
  magneticFluxDimension * electricCurrentDimension⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent magnetic flux through one turn. -/
abbrev MagneticFluxMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- A nonnegative, unit-independent self-inductance. -/
abbrev SelfInductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- Read any nonnegative dimensionful quantity in the coherent units induced by `units`. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a length in the coherent length unit induced by `units`. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  nonnegativeReadout units length

/-- Read an area in the coherent square-length unit induced by `units`. -/
def areaReadout (units : UnitChoices) (area : DimArea) : ℝ :=
  ((area units).val : ℝ)

/-- Read an electric-current magnitude in the coherent unit induced by `units`. -/
def currentReadout
    (units : UnitChoices) (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeReadout units current

/-- Read magnetic permeability in the coherent unit induced by `units`. -/
def permeabilityReadout
    (units : UnitChoices) (permeability : MagneticPermeabilityQuantity) : ℝ :=
  nonnegativeReadout units permeability

/-- Read magnetic flux density in the coherent unit induced by `units`. -/
def magneticFluxDensityReadout
    (units : UnitChoices) (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeReadout units field

/-- Read magnetic flux in the coherent unit induced by `units`. -/
def magneticFluxReadout
    (units : UnitChoices) (flux : MagneticFluxMagnitude) : ℝ :=
  nonnegativeReadout units flux

/-- Read self-inductance in the coherent unit induced by `units`. -/
def selfInductanceReadout
    (units : UnitChoices) (inductance : SelfInductanceQuantity) : ℝ :=
  nonnegativeReadout units inductance

/-- Read self-inductance in coherent-SI henries. -/
def selfInductanceInHenries (inductance : SelfInductanceQuantity) : ℝ :=
  selfInductanceReadout UnitChoices.SI inductance

/-- Read self-inductance in microhenries. -/
def selfInductanceInMicrohenries
    (inductance : SelfInductanceQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * selfInductanceInHenries inductance

/-! ## Toroidal geometry, physical model, and primary-raster vocabulary -/

/-- Geometries distinguished by the solenoid model. -/
inductive SolenoidGeometry where
  | toroidal
  | other
  deriving DecidableEq, Repr

/-- Winding idealizations used for the depicted wire. -/
inductive WindingModel where
  | closelyWound
  | other
  deriving DecidableEq, Repr

/-- Magnetic behavior of the toroidal core. -/
inductive MagneticCoreModel where
  | nonmagnetic
  | other
  deriving DecidableEq, Repr

/-- Cross-sectional approximations for the interior magnetic field. -/
inductive CrossSectionFieldModel where
  | uniformAcrossCrossSection
  | radiallyVarying
  deriving DecidableEq, Repr

/-- Colors directly visible in image `940.png`. -/
inductive FigureColor where
  | purple
  | beige
  | other
  deriving DecidableEq, Repr

/-- Physical-quantity labels printed in the supplied toroidal-solenoid figure. -/
inductive FigureQuantityLabel where
  | numberOfTurns
  | crossSectionalArea
  | meanRadius
  | windingCurrent
  deriving DecidableEq, Fintype, Repr

/-- The symbol printed for each labelled physical quantity. -/
def expectedPrintedSymbol : FigureQuantityLabel → String
  | .numberOfTurns => "N"
  | .crossSectionalArea => "A"
  | .meanRadius => "r"
  | .windingCurrent => "i"

/-!
Literal presentation facts from the primary raster.  The image contains only
symbolic parameter labels; it prints no numerical value for `N`, `A`, or `r`.
-/
structure ToroidalSolenoidFigure where
  toroidalCoreShown : Bool
  windingShownAroundCore : Bool
  windingColor : FigureColor
  coreColor : FigureColor
  quantityLabelShown : FigureQuantityLabel → Bool
  printedSymbol : FigureQuantityLabel → String
  meanRadiusArrowShown : Bool
  crossSectionPatchShown : Bool
  currentDirectionArrowsShown : Bool
  dashedMagneticFieldDirectionShown : Bool
  onlyFewTurnsShownAnnotation : Bool

/-!
Independent physical data for the solenoid.  In particular, `selfInductance`
is not defined from the desired closed form or from an answer choice.
-/
structure ToroidalSolenoidSetup where
  geometry : SolenoidGeometry
  windingModel : WindingModel
  coreModel : MagneticCoreModel
  crossSectionFieldModel : CrossSectionFieldModel
  meanRadius : LengthQuantity
  crossSectionalArea : DimArea
  numberOfTurns : ℕ
  windingCurrentMagnitude : ElectricCurrentMagnitude
  coreMagneticPermeability : MagneticPermeabilityQuantity
  interiorMagneticFluxDensity : MagneticFluxDensityMagnitude
  fluxThroughOneTurn : MagneticFluxMagnitude
  selfInductance : SelfInductanceQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  figure : ToroidalSolenoidFigure

/-! ## Scenario, figure evidence, parameter conditions, and governing laws -/

/-- The qualitative toroidal-solenoid model stated in the written problem. -/
structure MatchesWrittenToroidalSolenoidScenario
    (setup : ToroidalSolenoidSetup) : Prop where
  geometryIsToroidal : setup.geometry = .toroidal
  windingIsCloselyWound : setup.windingModel = .closelyWound
  coreIsNonmagnetic : setup.coreModel = .nonmagnetic
  fieldIsApproximatedUniformAcrossCrossSection :
    setup.crossSectionFieldModel = .uniformAcrossCrossSection

/-!
Labels, colors, arrows, and geometry directly read from `940.png`.  This
predicate contains no self-inductance value and no numerical parameter value.
-/
structure MatchesSuppliedToroidalSolenoidFigure
    (setup : ToroidalSolenoidSetup) : Prop where
  toroidalCoreIsShown : setup.figure.toroidalCoreShown = true
  windingIsShown : setup.figure.windingShownAroundCore = true
  windingIsPurple : setup.figure.windingColor = .purple
  coreIsBeige : setup.figure.coreColor = .beige
  allQuantityLabelsAreShown : ∀ label,
    setup.figure.quantityLabelShown label = true
  printedQuantitySymbols : ∀ label,
    setup.figure.printedSymbol label = expectedPrintedSymbol label
  radiusArrowIsShown : setup.figure.meanRadiusArrowShown = true
  areaPatchIsShown : setup.figure.crossSectionPatchShown = true
  currentArrowsAreShown : setup.figure.currentDirectionArrowsShown = true
  magneticFieldDirectionIsShown :
    setup.figure.dashedMagneticFieldDirectionShown = true
  fewTurnsAnnotationIsShown :
    setup.figure.onlyFewTurnsShownAnnotation = true

/-- Positivity and nondegeneracy required for the toroidal-solenoid derivation. -/
structure HasPhysicalToroidalSolenoidParameters
    (setup : ToroidalSolenoidSetup) : Prop where
  meanRadiusPositive :
    0 < lengthReadout UnitChoices.SI setup.meanRadius
  crossSectionalAreaPositive :
    0 < areaReadout UnitChoices.SI setup.crossSectionalArea
  numberOfTurnsPositive : 0 < setup.numberOfTurns
  windingCurrentPositive :
    0 < currentReadout UnitChoices.SI setup.windingCurrentMagnitude
  corePermeabilityPositive :
    0 < permeabilityReadout UnitChoices.SI setup.coreMagneticPermeability

/-!
The nonmagnetic core is calibrated, in coherent SI, to Physlib's
electromagnetic-system permeability parameter `μ₀`.  This premise contains no
self-inductance value.
-/
structure UsesVacuumMagneticPermeability
    (setup : ToroidalSolenoidSetup) : Prop where
  corePermeabilityAgreesWithElectromagneticSystem :
    permeabilityReadout UnitChoices.SI setup.coreMagneticPermeability =
      setup.electromagneticSystem.μ₀

/-!
The three governing relations used in the standard ideal-toroid derivation,
stated in every coherent unit system:

* `B (2 π r) = μ N I`, Ampere's circuital law on the mean circular path;
* `Φ = B A`, because the model treats `B` as uniform over the cross section;
* `L I = N Φ`, the defining self-inductance flux-linkage relation.

None of these fields states the requested closed form for `L`.
-/
structure SatisfiesIdealToroidalSolenoidLaws
    (setup : ToroidalSolenoidSetup) : Prop where
  ampereCircuitalLawOnMeanPath : ∀ units : UnitChoices,
    magneticFluxDensityReadout units setup.interiorMagneticFluxDensity *
        (2 * Real.pi * lengthReadout units setup.meanRadius) =
      permeabilityReadout units setup.coreMagneticPermeability *
        (setup.numberOfTurns : ℝ) *
        currentReadout units setup.windingCurrentMagnitude
  uniformCrossSectionFluxLaw : ∀ units : UnitChoices,
    magneticFluxReadout units setup.fluxThroughOneTurn =
      magneticFluxDensityReadout units setup.interiorMagneticFluxDensity *
        areaReadout units setup.crossSectionalArea
  selfInductanceFluxLinkageLaw : ∀ units : UnitChoices,
    selfInductanceReadout units setup.selfInductance *
        currentReadout units setup.windingCurrentMagnitude =
      (setup.numberOfTurns : ℝ) *
        magneticFluxReadout units setup.fluxThroughOneTurn

/-! ## Symbolic target and displayed choices -/

/-!
The governing relations imply the unit-covariant ideal-toroid result
`L = μ N² A / (2 π r)`.  This lemma is separate from the SI calibration of a
nonmagnetic core to `μ₀`.
-/
lemma selfInductance_eq_idealToroidFormula
    (setup : ToroidalSolenoidSetup)
    (_physical : HasPhysicalToroidalSolenoidParameters setup)
    (_laws : SatisfiesIdealToroidalSolenoidLaws setup) :
    ∀ units : UnitChoices,
      selfInductanceReadout units setup.selfInductance =
        permeabilityReadout units setup.coreMagneticPermeability *
            (setup.numberOfTurns : ℝ) ^ 2 *
            areaReadout units setup.crossSectionalArea /
          (2 * Real.pi * lengthReadout units setup.meanRadius) := by
  intro units
  have hcurrent_units_ne :
      currentReadout units setup.windingCurrentMagnitude ≠ 0 := by
    intro hzero
    have hscale :=
      congrArg
        (fun x : WithDim electricCurrentDimension NNReal => (x.val : ℝ))
        (setup.windingCurrentMagnitude.2 units UnitChoices.SI)
    simp only [WithDim.dim_apply, WithDim.smul_val] at hscale
    unfold currentReadout nonnegativeReadout at hzero
    have hzero' :
        (setup.windingCurrentMagnitude units).val = 0 := by
      exact_mod_cast hzero
    rw [hzero'] at hscale
    norm_num at hscale
    have hsi :
        currentReadout UnitChoices.SI setup.windingCurrentMagnitude = 0 := by
      unfold currentReadout nonnegativeReadout
      exact_mod_cast hscale
    exact (ne_of_gt _physical.windingCurrentPositive) hsi
  have hlength_units_ne :
      lengthReadout units setup.meanRadius ≠ 0 := by
    intro hzero
    have hscale :=
      congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
        (setup.meanRadius.2 units UnitChoices.SI)
    simp only [WithDim.dim_apply, WithDim.smul_val] at hscale
    unfold lengthReadout nonnegativeReadout at hzero
    have hzero' : (setup.meanRadius units).val = 0 := by
      exact_mod_cast hzero
    rw [hzero'] at hscale
    norm_num at hscale
    have hsi : lengthReadout UnitChoices.SI setup.meanRadius = 0 := by
      unfold lengthReadout nonnegativeReadout
      exact_mod_cast hscale
    exact (ne_of_gt _physical.meanRadiusPositive) hsi
  have hdenom_ne :
      2 * Real.pi * lengthReadout units setup.meanRadius ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hlength_units_ne
  rw [(eq_div_iff hcurrent_units_ne).2
        (_laws.selfInductanceFluxLinkageLaw units),
      _laws.uniformCrossSectionFluxLaw units,
      (eq_div_iff hdenom_ne).2 (_laws.ampereCircuitalLawOnMeanPath units)]
  field_simp

/-!
Blueprint label: `thm:physics:phyx_mini_0940:target`.

For the depicted closely wound toroidal solenoid on a nonmagnetic core, the
self-inductance in henries is `μ₀ N² A / (2 π r)` under the stated uniform-field
approximation.
-/
theorem problem_phyx_mini_0940
    (setup : ToroidalSolenoidSetup)
    (_scenario : MatchesWrittenToroidalSolenoidScenario setup)
    (_figure : MatchesSuppliedToroidalSolenoidFigure setup)
    (_physical : HasPhysicalToroidalSolenoidParameters setup)
    (_vacuum : UsesVacuumMagneticPermeability setup)
    (_laws : SatisfiesIdealToroidalSolenoidLaws setup) :
    selfInductanceInHenries setup.selfInductance =
      setup.electromagneticSystem.μ₀ *
          (setup.numberOfTurns : ℝ) ^ 2 *
          areaReadout UnitChoices.SI setup.crossSectionalArea /
        (2 * Real.pi * lengthReadout UnitChoices.SI setup.meanRadius) := by
  rw [selfInductanceInHenries, selfInductance_eq_idealToroidFormula
    setup _physical _laws UnitChoices.SI]
  rw [_vacuum.corePermeabilityAgreesWithElectromagneticSystem]

/-!
The source supplies no numerical readout for `N`, `A`, or `r`, so none of the
four displayed microhenry values follows from the available physical data.
The choices below are retained only as dataset metadata; in particular,
`recordedDatasetAnswer` is not asserted to satisfy `AnswerMatchesSelfInductance`.
-/

/-- Labels of the four answer choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed self-inductance readout for each choice, in microhenries. -/
def AnswerChoice.displayedSelfInductanceInMicrohenries :
    AnswerChoice → ℝ
  | .A => 22
  | .B => 40
  | .C => 75
  | .D => 28

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed choice agrees with the setup's physical self-inductance. -/
def AnswerMatchesSelfInductance
    (setup : ToroidalSolenoidSetup) (choice : AnswerChoice) : Prop :=
  selfInductanceInMicrohenries setup.selfInductance =
    choice.displayedSelfInductanceInMicrohenries

end PhyXMiniProblems.ProblemPhyXMini0940
