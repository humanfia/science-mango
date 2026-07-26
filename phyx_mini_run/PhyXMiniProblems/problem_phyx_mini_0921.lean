import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Area

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0921

open Dimension

/-!
# Mutual inductance of a long solenoid and a surrounding coil

The supplied raster shows a long, closely wound yellow primary solenoid of
length `l`, cross-sectional area `A`, and turn count `N₁`.  A gray secondary
coil of `N₂` turns surrounds the primary at its center.  The requested
physical quantity is their mutual inductance `M`.

Physical magnitudes are represented by Physlib's unit-independent
`Dimensionful (WithDim ...)` types.  Real numbers occur only at explicit
unit-readout boundaries, in turn counts, and in the displayed answer choices.

Assumption/target split:

* governing laws: the axial field law for a long solenoid, the uniform-flux
  law through one centered secondary turn, and the definition of mutual
  inductance through total flux linkage;
* previous-part results: none;
* figure/data readouts: the two coil roles and colors, the cylindrical coaxial
  geometry, central placement, and the labels `l`, `A`, `N₁`, and `N₂`;
* current target: `M = μ₀ N₁ N₂ A / l` (in coherent SI), with the recorded
  `25 μH` choice separately represented because the source supplies no
  numerical values for `l`, `A`, `N₁`, or `N₂`.

The mutual inductance is an independent field of the setup.  None of the
scenario, figure, calibration, or governing-law premises states the requested
closed form.
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

/-- Inductance is magnetic flux divided by electric current (henries). -/
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

/-- A nonnegative, unit-independent axial magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent magnetic flux through one turn. -/
abbrev MagneticFluxMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- A nonnegative, unit-independent mutual inductance. -/
abbrev MutualInductanceQuantity : Type :=
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

/-- Read an electric-current magnitude in the coherent current unit induced by `units`. -/
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

/-- Read mutual inductance in the coherent unit induced by `units`. -/
def mutualInductanceReadout
    (units : UnitChoices) (inductance : MutualInductanceQuantity) : ℝ :=
  nonnegativeReadout units inductance

/-- Read mutual inductance in coherent-SI henries. -/
def mutualInductanceInHenries (inductance : MutualInductanceQuantity) : ℝ :=
  mutualInductanceReadout UnitChoices.SI inductance

/-- Read mutual inductance in microhenries. -/
def mutualInductanceInMicrohenries
    (inductance : MutualInductanceQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * mutualInductanceInHenries inductance

/-! ## Coil roles, geometry, labels, and primary-raster content -/

/-- The inner primary winding and the outer secondary winding. -/
inductive CoilRole where
  | primary
  | secondary
  deriving DecidableEq, Fintype, Repr

/-- Electromagnetic idealizations assigned to the two depicted windings. -/
inductive CoilModel where
  | closelyWoundLongSolenoid
  | centeredSurroundingPickupCoil
  | other
  deriving DecidableEq, Repr

/-- The secondary coil's placement relative to the long solenoid. -/
inductive SecondaryPlacement where
  | surroundsSolenoidAtCenter
  | other
  deriving DecidableEq, Repr

/-- The magnetic medium used by the air-core/vacuum textbook model. -/
inductive MagneticMediumModel where
  | vacuumOrAir
  | other
  deriving DecidableEq, Repr

/-- Colors visibly used to distinguish the two windings in image `921.png`. -/
inductive CoilColor where
  | yellow
  | gray
  | other
  deriving DecidableEq, Repr

/-- The four physical-quantity labels printed in the raster. -/
inductive FigureQuantityLabel where
  | solenoidLength
  | crossSectionalArea
  | primaryTurnCount
  | secondaryTurnCount
  deriving DecidableEq, Fintype, Repr

/-- The symbol printed for each labelled quantity. -/
def expectedPrintedSymbol : FigureQuantityLabel → String
  | .solenoidLength => "l"
  | .crossSectionalArea => "A"
  | .primaryTurnCount => "N₁"
  | .secondaryTurnCount => "N₂"

/-!
Literal presentation facts from the primary raster.  It contains symbolic
labels but no numerical values of `l`, `A`, `N₁`, or `N₂`.
-/
structure TeslaCoilFigure where
  coilShown : CoilRole → Bool
  coilColor : CoilRole → CoilColor
  quantityLabelShown : FigureQuantityLabel → Bool
  printedSymbol : FigureQuantityLabel → String
  cylindricalSolenoidShown : Bool
  circularCrossSectionShown : Bool
  lengthDoubleArrowShown : Bool
  areaLeaderLineShown : Bool
  secondaryDrawnAroundPrimaryCenter : Bool

/-!
Independent physical data for the coupled coils.  In particular,
`mutualInductance` is not defined from the desired formula or from answer C.
-/
structure TeslaCoilSetup where
  coilModel : CoilRole → CoilModel
  secondaryPlacement : SecondaryPlacement
  magneticMedium : MagneticMediumModel
  solenoidLength : LengthQuantity
  crossSectionalArea : DimArea
  turnCount : CoilRole → ℕ
  primaryCurrentMagnitude : ElectricCurrentMagnitude
  mediumPermeability : MagneticPermeabilityQuantity
  interiorAxialFluxDensity : MagneticFluxDensityMagnitude
  fluxThroughOneSecondaryTurn : MagneticFluxMagnitude
  mutualInductance : MutualInductanceQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  figure : TeslaCoilFigure

/-! ## Scenario, figure evidence, parameter conditions, and governing laws -/

/-- The qualitative long-solenoid and centered pickup-coil model stated in the problem. -/
structure MatchesWrittenTeslaCoilScenario (setup : TeslaCoilSetup) : Prop where
  primaryIsCloselyWoundLongSolenoid :
    setup.coilModel .primary = .closelyWoundLongSolenoid
  secondaryIsCenteredPickupCoil :
    setup.coilModel .secondary = .centeredSurroundingPickupCoil
  secondarySurroundsCenter :
    setup.secondaryPlacement = .surroundsSolenoidAtCenter

/-!
The labels, colors, cylindrical geometry, and central placement directly read
from `921.png`.  No inductance value occurs here.
-/
structure MatchesSuppliedTeslaCoilFigure (setup : TeslaCoilSetup) : Prop where
  bothCoilsShown : ∀ role, setup.figure.coilShown role = true
  primaryWindingIsYellow : setup.figure.coilColor .primary = .yellow
  secondaryWindingIsGray : setup.figure.coilColor .secondary = .gray
  allQuantityLabelsShown : ∀ label,
    setup.figure.quantityLabelShown label = true
  printedQuantitySymbols : ∀ label,
    setup.figure.printedSymbol label = expectedPrintedSymbol label
  cylindricalBodyShown : setup.figure.cylindricalSolenoidShown = true
  crossSectionShown : setup.figure.circularCrossSectionShown = true
  lengthArrowShown : setup.figure.lengthDoubleArrowShown = true
  areaLeaderShown : setup.figure.areaLeaderLineShown = true
  secondaryShownAtCenter :
    setup.figure.secondaryDrawnAroundPrimaryCenter = true

/-- Positivity and nondegeneracy required for the coupled-coil derivation. -/
structure HasPhysicalTeslaCoilParameters (setup : TeslaCoilSetup) : Prop where
  solenoidLengthPositive :
    0 < lengthReadout UnitChoices.SI setup.solenoidLength
  crossSectionalAreaPositive :
    0 < areaReadout UnitChoices.SI setup.crossSectionalArea
  primaryTurnCountPositive :
    0 < setup.turnCount .primary
  secondaryTurnCountPositive :
    0 < setup.turnCount .secondary
  primaryCurrentPositive :
    0 < currentReadout UnitChoices.SI setup.primaryCurrentMagnitude
  permeabilityPositive :
    0 < permeabilityReadout UnitChoices.SI setup.mediumPermeability

/-!
The explicit textbook air-core idealization and its dimensionful permeability
calibration, in coherent SI, to Physlib's electromagnetic-system parameter
`μ₀`.  The source does not state the magnetic medium, so this is kept separate
from `MatchesWrittenTeslaCoilScenario`.  Neither field contains a mutual
inductance value.
-/
structure UsesVacuumMagneticPermeability (setup : TeslaCoilSetup) : Prop where
  mediumIsVacuumOrAir : setup.magneticMedium = .vacuumOrAir
  permeabilityAgreesWithElectromagneticSystem :
    permeabilityReadout UnitChoices.SI setup.mediumPermeability =
      setup.electromagneticSystem.μ₀

/-!
The three governing electromagnetic relations used in the standard
derivation, stated in every coherent unit system:

* `B = μ (N₁/l) I₁` inside a long closely wound solenoid;
* `Φ₂ = B A` through one centered, fully linked secondary turn;
* `M I₁ = N₂ Φ₂`, the defining flux-linkage relation for mutual inductance.

These laws do not state the requested closed form `M = μ N₁ N₂ A/l`.
-/
structure SatisfiesLongSolenoidMutualInductanceLaws
    (setup : TeslaCoilSetup) : Prop where
  longSolenoidAxialFieldLaw : ∀ units : UnitChoices,
    magneticFluxDensityReadout units setup.interiorAxialFluxDensity =
      permeabilityReadout units setup.mediumPermeability *
          (setup.turnCount .primary : ℝ) *
          currentReadout units setup.primaryCurrentMagnitude /
        lengthReadout units setup.solenoidLength
  uniformLinkedFluxLaw : ∀ units : UnitChoices,
    magneticFluxReadout units setup.fluxThroughOneSecondaryTurn =
      magneticFluxDensityReadout units setup.interiorAxialFluxDensity *
        areaReadout units setup.crossSectionalArea
  mutualInductanceFluxLinkageLaw : ∀ units : UnitChoices,
    mutualInductanceReadout units setup.mutualInductance *
        currentReadout units setup.primaryCurrentMagnitude =
      (setup.turnCount .secondary : ℝ) *
        magneticFluxReadout units setup.fluxThroughOneSecondaryTurn

/-! ## Symbolic target and displayed choices -/

/-!
The governing relations imply the unit-covariant symbolic result
`M = μ N₁ N₂ A/l`.  This lemma is kept separate from the vacuum calibration
used by the blueprint target.
-/
lemma mutualInductance_eq_longSolenoidFormula
    (setup : TeslaCoilSetup)
    (_physical : HasPhysicalTeslaCoilParameters setup)
    (_laws : SatisfiesLongSolenoidMutualInductanceLaws setup) :
    ∀ units : UnitChoices,
      mutualInductanceReadout units setup.mutualInductance =
        permeabilityReadout units setup.mediumPermeability *
            (setup.turnCount .primary : ℝ) *
            (setup.turnCount .secondary : ℝ) *
            areaReadout units setup.crossSectionalArea /
          lengthReadout units setup.solenoidLength := by
  intro units
  have readout_pos_of_SI {d : Dimension}
      (quantity : Dimensionful (WithDim d NNReal))
      (hquantity : 0 < nonnegativeReadout UnitChoices.SI quantity) :
      0 < nonnegativeReadout units quantity := by
    unfold nonnegativeReadout at hquantity ⊢
    rw [quantity.property UnitChoices.SI units]
    simp only [WithDim.smul_val]
    exact mul_pos (by exact_mod_cast
      UnitChoices.dimScale_pos UnitChoices.SI units d) hquantity
  have hcurrent :
      0 < currentReadout units setup.primaryCurrentMagnitude :=
    readout_pos_of_SI setup.primaryCurrentMagnitude
      _physical.primaryCurrentPositive
  have hlength :
      0 < lengthReadout units setup.solenoidLength :=
    readout_pos_of_SI setup.solenoidLength
      _physical.solenoidLengthPositive
  have hfield := _laws.longSolenoidAxialFieldLaw units
  have hflux := _laws.uniformLinkedFluxLaw units
  have hlink := _laws.mutualInductanceFluxLinkageLaw units
  rw [hflux, hfield] at hlink
  apply mul_right_cancel₀ (ne_of_gt hcurrent)
  rw [hlink]
  field_simp [ne_of_gt hlength]

/-!
Blueprint label: `thm:physics:phyx_mini_0921:target`.

For the depicted centered secondary around a long air-core solenoid, the
mutual inductance in henries is `μ₀ N₁ N₂ A/l`.
-/
theorem problem_phyx_mini_0921
    (setup : TeslaCoilSetup)
    (_scenario : MatchesWrittenTeslaCoilScenario setup)
    (_figure : MatchesSuppliedTeslaCoilFigure setup)
    (_physical : HasPhysicalTeslaCoilParameters setup)
    (_vacuum : UsesVacuumMagneticPermeability setup)
    (_laws : SatisfiesLongSolenoidMutualInductanceLaws setup) :
    mutualInductanceInHenries setup.mutualInductance =
      setup.electromagneticSystem.μ₀ *
          (setup.turnCount .primary : ℝ) *
          (setup.turnCount .secondary : ℝ) *
          areaReadout UnitChoices.SI setup.crossSectionalArea /
        lengthReadout UnitChoices.SI setup.solenoidLength := by
  rw [mutualInductanceInHenries,
    mutualInductance_eq_longSolenoidFormula setup _physical _laws
      UnitChoices.SI,
    _vacuum.permeabilityAgreesWithElectromagneticSystem]

/-- Labels of the four answer choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed mutual-inductance readout for each choice, in microhenries. -/
def AnswerChoice.displayedMutualInductanceInMicrohenries :
    AnswerChoice → ℝ
  | .A => 50
  | .B => 12.5
  | .C => 25
  | .D => 100

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The source omits numerical values for `l`, `A`, `N₁`, and `N₂`.  Consequently
the recorded choice is represented only as metadata: no declaration asserts
that the depicted symbolic setup has mutual inductance `25 μH`.
-/

end PhyXMiniProblems.ProblemPhyXMini0921
