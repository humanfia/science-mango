import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0896

open Dimension
open scoped BigOperators

/-!
# Net electrostatic force on the lower-right charge

The primary image shows three point charges at three corners of a dashed
rectangle.  A `+10 nC` charge is at the lower left, the queried `-10 nC`
charge is at the lower right, and a `+8.0 nC` charge is directly above it.
The lower horizontal separation is `3.0 cm`, and the right vertical separation
is `1.0 cm`.

Charges, lengths, and planar forces are represented by unit-independent
Physlib quantities.  The planar coordinates and the scalar values used in the
Coulomb law below are coherent-SI readouts (metres, coulombs, and newtons).

Assumption/target split:

* governing laws: the vector point-charge Coulomb force law and linear force
  superposition;
* previous-part results: none;
* figure/data readouts: the three charge labels and signs, the two dashed
  separations, their `3.0 cm` and `1.0 cm` labels, and the three corner
  coordinates;
* current target conclusions: the net force magnitude lies in the rounding
  interval for `7.3 * 10^-3 N`, and hence matches recorded answer C at
  resolution `10^-4 N`.

Neither the target magnitude nor the selected answer is stored in the setup
or in any premise structure.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent force vector in the plane of the figure. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the three printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two dimension labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI planar-force vector, whose coordinates are in newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- Euclidean magnitude of a planar physical force, in newtons. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-! ## Figure labels and independent physical setup -/

/-- The three occupied corners in the supplied image. -/
inductive ChargeSite where
  | lowerLeft
  | lowerRight
  | upperRight
  deriving DecidableEq, Fintype, Repr

/-- The two charges exerting force on the queried lower-right charge. -/
inductive SourceCharge where
  | lowerLeftPositive
  | upperRightPositive
  deriving DecidableEq, Fintype, Repr

/-- The site occupied by each source charge. -/
def sourceSite : SourceCharge → ChargeSite
  | .lowerLeftPositive => .lowerLeft
  | .upperRightPositive => .upperRight

/-- The red and teal circle fills used in the primary raster. -/
inductive FigureChargeColor where
  | red
  | teal
  deriving DecidableEq, Repr

/-- The sign glyph drawn inside each charge marker. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Expected marker colour at each occupied corner. -/
def expectedChargeColor : ChargeSite → FigureChargeColor
  | .lowerLeft => .red
  | .lowerRight => .teal
  | .upperRight => .red

/-- Expected sign glyph at each occupied corner. -/
def expectedChargeSign : ChargeSite → FigureChargeSign
  | .lowerLeft => .plus
  | .lowerRight => .minus
  | .upperRight => .plus

/-- Signed nanocoulomb value printed beside each charge marker. -/
def expectedChargeInNanocoulombs : ChargeSite → ℝ
  | .lowerLeft => 10
  | .lowerRight => -10
  | .upperRight => 8

/-- The two dashed separations carrying numerical labels. -/
inductive FigureSeparation where
  | lowerHorizontal
  | rightVertical
  deriving DecidableEq, Fintype, Repr

/-- Literal presentation data transcribed from image `896.png`. -/
structure ThreePointChargeFigure where
  chargeCircleShown : ChargeSite → Bool
  chargeColor : ChargeSite → FigureChargeColor
  chargeSign : ChargeSite → FigureChargeSign
  printedChargeNanocoulombs : ChargeSite → ℝ
  dashedSeparationShown : FigureSeparation → Bool
  dimensionLabelCentimeters : FigureSeparation → ℝ

/-- Turn a planar `Space 2` point into its explicitly metre-valued vector. -/
def positionVectorInMeters (point : Space 2) : EuclideanSpace ℝ (Fin 2) :=
  !₂[point.val 0, point.val 1]

/-!
The independent physical objects in the electrostatic setup.  The pair-force
vectors and resultant force are observables constrained only by the governing
laws below; no numerical answer value is built into them.
-/
structure ThreePointChargeSetup where
  figure : ThreePointChargeFigure
  horizontalSeparation : LengthQuantity
  verticalSeparation : LengthQuantity
  position : ChargeSite → Space 2
  charge : ChargeSite → SignedChargeQuantity
  forceTarget : ChargeSite
  electromagneticSystem : Electromagnetism.EMSystem
  forceOnTargetFrom : SourceCharge → PlanarForceQuantity
  netForceOnTarget : PlanarForceQuantity

/-- Displacement from a named source to the force target, in metres. -/
def displacementFromSourceToTargetInMeters
    (setup : ThreePointChargeSetup)
    (source : SourceCharge) : EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters (setup.position setup.forceTarget) -
    positionVectorInMeters (setup.position (sourceSite source))

/-! ## Question target, primary-image evidence, and physical parameters -/

/-- The question asks for the force on the lower-right `-10 nC` charge. -/
structure MatchesQuestionTarget (setup : ThreePointChargeSetup) : Prop where
  queriedChargeIsLowerRight : setup.forceTarget = .lowerRight

/-!
All literal labels and geometric readouts from the primary raster.  In
particular, the `3.0 cm` label belongs to the lower horizontal segment between
the `+10 nC` and `-10 nC` charges, while the `1.0 cm` label belongs to the
right vertical segment.
-/
structure MatchesSuppliedThreeChargeFigure
    (setup : ThreePointChargeSetup) : Prop where
  allChargeCirclesShown : ∀ site,
    setup.figure.chargeCircleShown site = true
  markerColors : ∀ site,
    setup.figure.chargeColor site = expectedChargeColor site
  markerSignGlyphs : ∀ site,
    setup.figure.chargeSign site = expectedChargeSign site
  printedChargeLabels : ∀ site,
    setup.figure.printedChargeNanocoulombs site =
      expectedChargeInNanocoulombs site
  physicalChargesMatchPrintedLabels : ∀ site,
    chargeInNanocoulombs (setup.charge site) =
      setup.figure.printedChargeNanocoulombs site
  bothDashedSeparationsShown : ∀ separation,
    setup.figure.dashedSeparationShown separation = true
  lowerHorizontalLabelIsThreeCentimeters :
    setup.figure.dimensionLabelCentimeters .lowerHorizontal = 3
  rightVerticalLabelIsOneCentimeter :
    setup.figure.dimensionLabelCentimeters .rightVertical = 1
  horizontalLengthMatchesLabel :
    lengthInCentimeters setup.horizontalSeparation =
      setup.figure.dimensionLabelCentimeters .lowerHorizontal
  verticalLengthMatchesLabel :
    lengthInCentimeters setup.verticalSeparation =
      setup.figure.dimensionLabelCentimeters .rightVertical
  lowerLeftAtOrigin :
    positionVectorInMeters (setup.position .lowerLeft) = !₂[0, 0]
  lowerRightCoordinates :
    positionVectorInMeters (setup.position .lowerRight) =
      !₂[lengthInMeters setup.horizontalSeparation, 0]
  upperRightCoordinates :
    positionVectorInMeters (setup.position .upperRight) =
      !₂[lengthInMeters setup.horizontalSeparation,
        lengthInMeters setup.verticalSeparation]

/-!
The standard free-space calibration of Coulomb's constant.  Its scalar
readout has coherent-SI units `N m²/C²` in the force law below.
-/
structure UsesVacuumCoulombConstant
    (setup : ThreePointChargeSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity and source-target separation for the depicted branch. -/
structure HasPhysicalThreeChargeParameters
    (setup : ThreePointChargeSetup) : Prop where
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparation
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparation
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  eachSourceSeparatedFromTarget : ∀ source,
    0 < ‖displacementFromSourceToTargetInMeters setup source‖

/-! ## Governing electrostatic laws -/

/-!
For source charge `q_s`, target charge `q_t`, and displacement `r` from the
source to the target, the force on the target is
`k q_s q_t r / ‖r‖³`.  The signs of the charges therefore determine attraction
or repulsion.  This relation contains no requested force magnitude.
-/
structure SatisfiesPointChargeCoulombForceLaw
    (setup : ThreePointChargeSetup) : Prop where
  forceFromEachSource : ∀ source,
    forceVectorInNewtons (setup.forceOnTargetFrom source) =
      (setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge (sourceSite source)) *
          chargeInCoulombs (setup.charge setup.forceTarget) /
        ‖displacementFromSourceToTargetInMeters setup source‖ ^ 3) •
          displacementFromSourceToTargetInMeters setup source

/-- The net force on the queried charge is the vector sum of both pair forces. -/
structure SatisfiesElectrostaticForceSuperposition
    (setup : ThreePointChargeSetup) : Prop where
  netForceIsPairForceSum :
    forceVectorInNewtons setup.netForceOnTarget =
      ∑ source : SourceCharge,
        forceVectorInNewtons (setup.forceOnTargetFrom source)

/-! ## Derived force and displayed-answer target -/

/-- Labels attached to the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitude in newtons printed by each answer choice. -/
def AnswerChoice.forceMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 29 / 4000
  | .B => 127 / 20000
  | .C => 73 / 10000
  | .D => 133 / 100000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
`displayed` is a nearest-multiple-of-`quantum` rounding of `actual`.  Requiring
the displayed value to lie on the quantum grid distinguishes the two-significant-
figure answer `7.3 * 10^-3 N` from an unrounded decimal nearby.
-/
def RoundsToNearestQuantum
    (actual displayed quantum : ℝ) : Prop :=
  0 < quantum ∧
    ∃ n : ℤ,
      displayed = (n : ℝ) * quantum ∧
      displayed - quantum / 2 ≤ actual ∧
      actual < displayed + quantum / 2

/-!
Coulomb's law and superposition give the net force as a sum depending only on
the two sources, the target charge, their positions, and Coulomb's constant.
-/
lemma netForceVector_eq_coulombSum
    (setup : ThreePointChargeSetup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombForceLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup) :
    forceVectorInNewtons setup.netForceOnTarget =
      ∑ source : SourceCharge,
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge (sourceSite source)) *
            chargeInCoulombs (setup.charge setup.forceTarget) /
          ‖displacementFromSourceToTargetInMeters setup source‖ ^ 3) •
            displacementFromSourceToTargetInMeters setup source := by
  rw [_superposition.netForceIsPairForceSum]
  apply Finset.sum_congr rfl
  intro source _
  exact _coulomb.forceFromEachSource source

/-!
For the charge and distance readouts in the image, the unrounded magnitude is
approximately `7.2591 * 10^-3 N`.  These bounds are exactly the interval that
rounds to `7.3 * 10^-3 N` at resolution `10^-4 N`.
-/
lemma netForceMagnitude_numericalBounds
    (setup : ThreePointChargeSetup)
    (_target : MatchesQuestionTarget setup)
    (_figure : MatchesSuppliedThreeChargeFigure setup)
    (_constant : UsesVacuumCoulombConstant setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombForceLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup) :
    (29 / 4000 : ℝ) < forceMagnitudeInNewtons setup.netForceOnTarget ∧
      forceMagnitudeInNewtons setup.netForceOnTarget < 147 / 20000 := by
  have hHorizontal : lengthInMeters setup.horizontalSeparation = 3 / 100 := by
    have h := _figure.horizontalLengthMatchesLabel
    rw [_figure.lowerHorizontalLabelIsThreeCentimeters] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hVertical : lengthInMeters setup.verticalSeparation = 1 / 100 := by
    have h := _figure.verticalLengthMatchesLabel
    rw [_figure.rightVerticalLabelIsOneCentimeter] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hChargeLowerLeft :
      chargeInCoulombs (setup.charge .lowerLeft) = 1 / 100000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .lowerLeft
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hChargeLowerRight :
      chargeInCoulombs (setup.charge .lowerRight) = -(1 / 100000000) := by
    have h := _figure.physicalChargesMatchPrintedLabels .lowerRight
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hChargeUpperRight :
      chargeInCoulombs (setup.charge .upperRight) = 1 / 125000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .upperRight
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hDisplacementLowerLeft :
      displacementFromSourceToTargetInMeters setup .lowerLeftPositive =
        !₂[(3 : ℝ) / 100, 0] := by
    rw [displacementFromSourceToTargetInMeters,
      _target.queriedChargeIsLowerRight, sourceSite,
      _figure.lowerRightCoordinates, _figure.lowerLeftAtOrigin, hHorizontal]
    ext i
    fin_cases i <;> norm_num
  have hDisplacementUpperRight :
      displacementFromSourceToTargetInMeters setup .upperRightPositive =
        !₂[(0 : ℝ), -(1 : ℝ) / 100] := by
    rw [displacementFromSourceToTargetInMeters,
      _target.queriedChargeIsLowerRight, sourceSite,
      _figure.lowerRightCoordinates, _figure.upperRightCoordinates,
      hHorizontal, hVertical]
    ext i
    fin_cases i <;> norm_num
  have hNormLowerLeft :
      ‖displacementFromSourceToTargetInMeters setup .lowerLeftPositive‖ =
        (3 : ℝ) / 100 := by
    rw [hDisplacementLowerLeft, EuclideanSpace.norm_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hNormUpperRight :
      ‖displacementFromSourceToTargetInMeters setup .upperRightPositive‖ =
        (1 : ℝ) / 100 := by
    rw [hDisplacementUpperRight, EuclideanSpace.norm_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hSourceSum
      (f : SourceCharge → EuclideanSpace ℝ (Fin 2)) :
      ∑ source : SourceCharge, f source =
        f .lowerLeftPositive + f .upperRightPositive := by
    rw [show (Finset.univ : Finset SourceCharge) =
      {.lowerLeftPositive, .upperRightPositive} by decide]
    simp
  have hForce := netForceVector_eq_coulombSum
    setup _physical _coulomb _superposition
  simp only [sourceSite] at hForce
  rw [hSourceSum, _constant.coulombConstantCalibration,
    _target.queriedChargeIsLowerRight,
    hChargeLowerLeft, hChargeLowerRight, hChargeUpperRight,
    hNormLowerLeft, hNormUpperRight,
    hDisplacementLowerLeft, hDisplacementUpperRight] at hForce
  have hForceComponents :
      forceVectorInNewtons setup.netForceOnTarget =
        !₂[-(89875517923 : ℝ) / 90000000000000,
          (89875517923 : ℝ) / 12500000000000] := by
    rw [hForce]
    ext i
    fin_cases i <;> norm_num
  have hMagnitudeSq :
      forceMagnitudeInNewtons setup.netForceOnTarget ^ 2 =
        (-(89875517923 : ℝ) / 90000000000000) ^ 2 +
          ((89875517923 : ℝ) / 12500000000000) ^ 2 := by
    rw [forceMagnitudeInNewtons, hForceComponents,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    norm_num
  have hMagnitudeNonnegative :
      0 ≤ forceMagnitudeInNewtons setup.netForceOnTarget :=
    norm_nonneg _
  have hLowerSq :
      ((29 : ℝ) / 4000) ^ 2 <
        forceMagnitudeInNewtons setup.netForceOnTarget ^ 2 := by
    rw [hMagnitudeSq]
    norm_num
  have hUpperSq :
      forceMagnitudeInNewtons setup.netForceOnTarget ^ 2 <
        ((147 : ℝ) / 20000) ^ 2 := by
    rw [hMagnitudeSq]
    norm_num
  constructor <;> nlinarith

/-!
The two perpendicular attractive forces have magnitudes about `0.999 mN` and
`7.190 mN`; their vector sum has magnitude about `7.259 mN`.  Consequently it
rounds to `7.3 * 10^-3 N`, the value displayed by recorded answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0896:target`.
-/
theorem problem_phyx_mini_0896
    (setup : ThreePointChargeSetup)
    (hTarget : MatchesQuestionTarget setup)
    (hFigure : MatchesSuppliedThreeChargeFigure setup)
    (hConstant : UsesVacuumCoulombConstant setup)
    (hPhysical : HasPhysicalThreeChargeParameters setup)
    (hCoulomb : SatisfiesPointChargeCoulombForceLaw setup)
    (hSuperposition : SatisfiesElectrostaticForceSuperposition setup) :
    (29 / 4000 : ℝ) < forceMagnitudeInNewtons setup.netForceOnTarget ∧
      forceMagnitudeInNewtons setup.netForceOnTarget < 147 / 20000 ∧
      RoundsToNearestQuantum
        (forceMagnitudeInNewtons setup.netForceOnTarget)
        recordedDatasetAnswer.forceMagnitudeInNewtons
        (1 / 10000) := by
  have hBounds := netForceMagnitude_numericalBounds setup hTarget hFigure
    hConstant hPhysical hCoulomb hSuperposition
  refine ⟨hBounds.1, hBounds.2, ?_⟩
  unfold RoundsToNearestQuantum
  constructor
  · norm_num
  · refine ⟨73, ?_, ?_, ?_⟩
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.forceMagnitudeInNewtons]
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.forceMagnitudeInNewtons]
      exact le_of_lt hBounds.1
    · norm_num [recordedDatasetAnswer,
        AnswerChoice.forceMagnitudeInNewtons]
      exact hBounds.2

end PhyXMiniProblems.ProblemPhyXMini0896
