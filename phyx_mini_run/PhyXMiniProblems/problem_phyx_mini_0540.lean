import Mathlib.Geometry.Euclidean.Triangle
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0540

open Dimension

/-!
# Momentum of the neutron in `Sigma+ -> pi+ + n`

The primary image shows an incoming curved `Sigma+` track ending at a decay
vertex, an outgoing curved `pi+` track, and a dashed reconstructed neutron
momentum ray.  The field is uniform and points out of the page.  The angle
`theta` is the angle from the forward tangent of the incoming `Sigma+`
momentum to the outgoing pion momentum.

Lengths, charges, magnetic-field strength, masses, and planar momenta are
unit-independent Physlib quantities.  Real numbers occur only after an
explicit readout in coherent SI or in the requested `MeV/c` unit.  The
charged-track law and momentum conservation are assumptions; the numerical
neutron answer occurs only in the displayed-choice table and final target.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- The SI dimension `M T⁻¹ C⁻¹` of magnetic flux density. -/
def magneticFieldStrengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent rest mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative magnetic-field-strength magnitude. -/
abbrev MagneticFieldStrengthQuantity : Type :=
  Dimensionful (WithDim magneticFieldStrengthDimension NNReal)

/-!
A unit-independent physical two-momentum.  Physlib's `Momentum 2` has the
correct `M L T⁻¹` dimension and stores its two components in the chosen unit
system.
-/
abbrev PlanarMomentumQuantity : Type :=
  Dimensionful (Momentum 2)

/-- Read a physical length in coherent SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a charge magnitude in coherent SI coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read magnetic flux density in coherent SI teslas. -/
def magneticFieldStrengthInTeslas
    (strength : MagneticFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-!
Read a physical two-momentum in arbitrary coherent units and equip its two
components with Mathlib's Euclidean norm and inner product.
-/
def momentumVectorReadout
    (units : UnitChoices)
    (momentum : PlanarMomentumQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (momentum units).val

/-- Planar momentum-vector readout in kilogram-metres per second. -/
def momentumVectorInSI
    (momentum : PlanarMomentumQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  momentumVectorReadout UnitChoices.SI momentum

/-- Momentum magnitude in kilogram-metres per second. -/
def momentumMagnitudeInKilogramMetersPerSecond
    (momentum : PlanarMomentumQuantity) : ℝ :=
  ‖momentumVectorInSI momentum‖

/-- The SI metre-per-second readout of Physlib's exact speed of light. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- The SI joule readout of Physlib's exact electron volt. -/
def electronVoltInJoules : ℝ :=
  (DimEnergy.electronVolt UnitChoices.SI).val

/-!
Convert an SI momentum magnitude to `MeV/c`, using
`p[MeV/c] = p[kg m/s] * c / (10^6 eV[J])`.
-/
def momentumMagnitudeInMeVPerC
    (momentum : PlanarMomentumQuantity) : ℝ :=
  momentumMagnitudeInKilogramMetersPerSecond momentum *
      speedOfLightInMetersPerSecond /
    ((10 : ℝ) ^ 6 * electronVoltInJoules)

/-! ## Particle, apparatus, and primary-figure vocabulary -/

/-- The three particle species participating in the observed decay. -/
inductive ParticleSpecies where
  | sigmaPlus
  | pionPlus
  | neutron
  deriving DecidableEq, Fintype, Repr

/-- Charged tracks whose curvature radii are measured in the chamber. -/
inductive ChargedTrack where
  | sigmaPlus
  | pionPlus
  deriving DecidableEq, Fintype, Repr

/-- The particle represented by each charged track. -/
def ChargedTrack.particle : ChargedTrack → ParticleSpecies
  | .sigmaPlus => .sigmaPlus
  | .pionPlus => .pionPlus

/-- The sign class of a particle's electric charge. -/
inductive ChargeSign where
  | positive
  | neutral
  | negative
  deriving DecidableEq, Repr

/-- The apparatus medium in which the tracks are observed. -/
inductive ObservationMedium where
  | bubbleChamber
  | other
  deriving DecidableEq, Repr

/-- Directions normal to the two-dimensional page. -/
inductive PageNormalDirection where
  | outOfPage
  | intoPage
  deriving DecidableEq, Repr

/-- Text and symbols visibly printed in the supplied raster. -/
inductive FigureLabel where
  | sigmaPlus
  | pionPlus
  | neutronN
  | decayAngleTheta
  deriving DecidableEq, Fintype, Repr

/-- Geometric elements visible in the supplied raster. -/
inductive FigureElement where
  | sigmaCurvedTrack
  | pionCurvedTrack
  | inferredNeutronMomentumRay
  | forwardSigmaTangentReference
  | decayVertex
  | thetaAngleArc
  deriving DecidableEq, Fintype, Repr

/-- Stroke styles used to distinguish tracks and inferred rays. -/
inductive FigureStrokeStyle where
  | solidCurved
  | solidStraight
  | dashedStraight
  deriving DecidableEq, Repr

/-- Whether a momentum arrow enters or leaves the decay vertex. -/
inductive ArrowFlowAtVertex where
  | incoming
  | outgoing
  deriving DecidableEq, Repr

/-!
Presentation-level data transcribed from image 540.  The dashed neutron line
is a reconstructed momentum ray, not an ionization track in the chamber.
-/
structure BubbleChamberDecayFigure where
  labelShown : FigureLabel → Bool
  elementShown : FigureElement → Bool
  particleStrokeStyle : ParticleSpecies → FigureStrokeStyle
  momentumArrowFlow : ParticleSpecies → ArrowFlowAtVertex
  verticalReferenceIsForwardSigmaTangent : Bool

/-- The unit vector normal to the page in its positive, outward direction. -/
def outOfPageDirection : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (2 : Fin 3) 1

/-!
All independent physical quantities in the decay setup.  Rest masses are
retained because the surrounding scenario aims eventually to determine the
`Sigma+` mass, although the present subquestion asks only for neutron
momentum.  No numerical neutron momentum is stored here.
-/
structure SigmaPlusDecaySetup where
  observationMedium : ObservationMedium
  restMass : ParticleSpecies → MassQuantity
  chargeSign : ParticleSpecies → ChargeSign
  chargeMagnitude : ParticleSpecies → ChargeMagnitudeQuantity
  momentumAtDecay : ParticleSpecies → PlanarMomentumQuantity
  trackRadius : ChargedTrack → LengthQuantity
  magneticFieldStrength : MagneticFieldStrengthQuantity
  appliedMagneticField : Electromagnetism.MagneticField 3
  fieldDirection : PageNormalDirection
  chargedTracksLieInPage : Bool
  neutronLeavesNoIonizationTrack : Bool
  figure : BubbleChamberDecayFigure

/-! ## Scenario, numerical data, figure evidence, and governing laws -/

/-!
Categorical content of the physical scenario.  The two charged particles are
positive, the neutron is neutral and invisible in the chamber, and all
momenta lie in the page perpendicular to the field.
-/
structure MatchesSigmaPlusDecayScenario
    (setup : SigmaPlusDecaySetup) : Prop where
  observedInBubbleChamber :
    setup.observationMedium = .bubbleChamber
  sigmaChargeIsPositive :
    setup.chargeSign .sigmaPlus = .positive
  pionChargeIsPositive :
    setup.chargeSign .pionPlus = .positive
  neutronChargeIsNeutral :
    setup.chargeSign .neutron = .neutral
  tracksLieInImagePlane :
    setup.chargedTracksLieInPage = true
  neutronTrackIsInvisible :
    setup.neutronLeavesNoIonizationTrack = true

/-!
Numerical measurements stated in the problem.  The field is `1.15 T`, the
curvature radii are `1.99 m` and `0.580 m`, and the momentum angle is
`64.5 degrees = 43*pi/120` radians.  No neutron momentum value occurs here.
-/
structure MatchesProblemReadouts
    (setup : SigmaPlusDecaySetup) : Prop where
  magneticFieldDirectedOutOfPage :
    setup.fieldDirection = .outOfPage
  magneticFieldTeslaReadout :
    magneticFieldStrengthInTeslas setup.magneticFieldStrength = 23 / 20
  sigmaRadiusMeterReadout :
    lengthInMeters (setup.trackRadius .sigmaPlus) = 199 / 100
  pionRadiusMeterReadout :
    lengthInMeters (setup.trackRadius .pionPlus) = 29 / 50
  sigmaPionAngleRadians :
    InnerProductGeometry.angle
        (momentumVectorInSI (setup.momentumAtDecay .sigmaPlus))
        (momentumVectorInSI (setup.momentumAtDecay .pionPlus)) =
      43 * Real.pi / 120

/-!
Qualitative geometry read directly from the primary image.  In particular,
the incoming `Sigma+` arrow terminates at the decay vertex, while the pion
and reconstructed neutron arrows leave it.
-/
structure MatchesSuppliedFigure
    (setup : SigmaPlusDecaySetup) : Prop where
  everyNamedLabelShown :
    ∀ label, setup.figure.labelShown label = true
  everyNamedElementShown :
    ∀ element, setup.figure.elementShown element = true
  sigmaTrackIsSolidAndCurved :
    setup.figure.particleStrokeStyle .sigmaPlus = .solidCurved
  pionTrackIsSolidAndCurved :
    setup.figure.particleStrokeStyle .pionPlus = .solidCurved
  neutronRayIsDashedAndStraight :
    setup.figure.particleStrokeStyle .neutron = .dashedStraight
  sigmaArrowEntersVertex :
    setup.figure.momentumArrowFlow .sigmaPlus = .incoming
  pionArrowLeavesVertex :
    setup.figure.momentumArrowFlow .pionPlus = .outgoing
  neutronArrowLeavesVertex :
    setup.figure.momentumArrowFlow .neutron = .outgoing
  thetaUsesForwardSigmaTangent :
    setup.figure.verticalReferenceIsForwardSigmaTangent = true

/-!
Standard elementary-charge calibration.  Both positive charged particles
have magnitude `e`, while the neutral neutron has zero charge magnitude.
-/
structure UsesStandardParticleCharges
    (setup : SigmaPlusDecaySetup) : Prop where
  sigmaChargeMagnitudeCoulombs :
    chargeInCoulombs (setup.chargeMagnitude .sigmaPlus) =
      (1602176634 / 10 ^ 28 : ℝ)
  pionChargeMagnitudeCoulombs :
    chargeInCoulombs (setup.chargeMagnitude .pionPlus) =
      (1602176634 / 10 ^ 28 : ℝ)
  neutronChargeMagnitudeCoulombs :
    chargeInCoulombs (setup.chargeMagnitude .neutron) = 0

/-! Positivity and nondegeneracy conditions for the observed event. -/
structure HasPhysicalDecayParameters
    (setup : SigmaPlusDecaySetup) : Prop where
  everyRestMassPositive :
    ∀ species, 0 < ((setup.restMass species UnitChoices.SI).val : ℝ)
  magneticFieldStrengthPositive :
    0 < magneticFieldStrengthInTeslas setup.magneticFieldStrength
  everyMeasuredRadiusPositive :
    ∀ track, 0 < lengthInMeters (setup.trackRadius track)
  sigmaChargeMagnitudePositive :
    0 < chargeInCoulombs (setup.chargeMagnitude .sigmaPlus)
  pionChargeMagnitudePositive :
    0 < chargeInCoulombs (setup.chargeMagnitude .pionPlus)
  sigmaMomentumNonzero :
    momentumVectorInSI (setup.momentumAtDecay .sigmaPlus) ≠ 0
  pionMomentumNonzero :
    momentumVectorInSI (setup.momentumAtDecay .pionPlus) ≠ 0

/-!
Physlib's electromagnetic field uses real vector coordinates.  This premise
states that those coordinates are tesla readouts and that the field is the
uniform vector `B z-hat` at every spacetime point.
-/
structure IsUniformMagneticFieldOutOfPage
    (setup : SigmaPlusDecaySetup) : Prop where
  fieldAtEverySpacetimePoint :
    ∀ time position,
      setup.appliedMagneticField time position =
        magneticFieldStrengthInTeslas setup.magneticFieldStrength •
          outOfPageDirection

/-!
For each positive charged track perpendicular to a uniform field, the
relativistic momentum magnitude obeys `p = q B R`.  This is the governing
magnetic-curvature law, not a specialized neutron-momentum formula.
-/
structure SatisfiesChargedTrackCurvatureLaw
    (setup : SigmaPlusDecaySetup) : Prop where
  sigmaMomentumFromCurvature :
    momentumMagnitudeInKilogramMetersPerSecond
        (setup.momentumAtDecay .sigmaPlus) =
      chargeInCoulombs (setup.chargeMagnitude .sigmaPlus) *
        magneticFieldStrengthInTeslas setup.magneticFieldStrength *
        lengthInMeters (setup.trackRadius .sigmaPlus)
  pionMomentumFromCurvature :
    momentumMagnitudeInKilogramMetersPerSecond
        (setup.momentumAtDecay .pionPlus) =
      chargeInCoulombs (setup.chargeMagnitude .pionPlus) *
        magneticFieldStrengthInTeslas setup.magneticFieldStrength *
        lengthInMeters (setup.trackRadius .pionPlus)

/-!
Three-momentum conservation at the two-body decay vertex, restricted to the
two-dimensional chamber plane.  It is required in every coherent unit system
and contains no numerical neutron answer.
-/
structure SatisfiesDecayMomentumConservation
    (setup : SigmaPlusDecaySetup) : Prop where
  momentumConservation :
    ∀ units : UnitChoices,
      momentumVectorReadout units (setup.momentumAtDecay .sigmaPlus) =
        momentumVectorReadout units (setup.momentumAtDecay .pionPlus) +
          momentumVectorReadout units (setup.momentumAtDecay .neutron)

/-! ## Derived relation, displayed choices, and current target -/

/-!
Momentum conservation and the measured parent-pion angle imply the cosine
rule for the neutron momentum.  This is a derived intermediate conclusion,
not a field of any premise structure.
-/
lemma neutronMomentumCosineRelation
    (setup : SigmaPlusDecaySetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalDecayParameters setup)
    (hConservation : SatisfiesDecayMomentumConservation setup) :
    momentumMagnitudeInKilogramMetersPerSecond
          (setup.momentumAtDecay .neutron) ^ 2 =
      momentumMagnitudeInKilogramMetersPerSecond
            (setup.momentumAtDecay .sigmaPlus) ^ 2 +
        momentumMagnitudeInKilogramMetersPerSecond
            (setup.momentumAtDecay .pionPlus) ^ 2 -
        2 *
          momentumMagnitudeInKilogramMetersPerSecond
            (setup.momentumAtDecay .sigmaPlus) *
          momentumMagnitudeInKilogramMetersPerSecond
            (setup.momentumAtDecay .pionPlus) *
          Real.cos (43 * Real.pi / 120) := by
  have hMomentum :
      momentumVectorInSI (setup.momentumAtDecay .neutron) =
        momentumVectorInSI (setup.momentumAtDecay .sigmaPlus) -
          momentumVectorInSI (setup.momentumAtDecay .pionPlus) := by
    change
      momentumVectorReadout UnitChoices.SI (setup.momentumAtDecay .neutron) =
        momentumVectorReadout UnitChoices.SI (setup.momentumAtDecay .sigmaPlus) -
          momentumVectorReadout UnitChoices.SI (setup.momentumAtDecay .pionPlus)
    rw [hConservation.momentumConservation UnitChoices.SI]
    abel
  have hCosineRule :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
      (momentumVectorInSI (setup.momentumAtDecay .sigmaPlus))
      (momentumVectorInSI (setup.momentumAtDecay .pionPlus))
  rw [hReadouts.sigmaPionAngleRadians] at hCosineRule
  simpa [momentumMagnitudeInKilogramMetersPerSecond, hMomentum, pow_two] using hCosineRule

/-- Labels of the four momentum values displayed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed neutron-momentum candidates, as numerical `MeV/c` values. -/
def displayedMomentumInMeVPerC : AnswerChoice → ℝ
  | .A => 710
  | .B => 509
  | .C => 533
  | .D => 626

/-!
A displayed choice is correct when its `MeV/c` readout is at least as close
to the physically derived neutron momentum as every other displayed choice.
This comparison is appropriate for the rounded measured inputs and avoids
asserting that the underlying physical magnitude equals a whole number
exactly.
-/
def IsClosestDisplayedMomentumChoice
    (setup : SigmaPlusDecaySetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    |momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) -
        displayedMomentumInMeVPerC choice| ≤
      |momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) -
        displayedMomentumInMeVPerC otherChoice|

/-!
Blueprint: `thm:physics:phyx_mini_0540:target`.

The neutron momentum obtained from the two charged-track curvatures,
two-body momentum conservation, and the `64.5 degree` angle is closest to
`626 MeV/c`, hence the recorded answer is choice D.
-/
theorem problem_phyx_mini_0540
    (setup : SigmaPlusDecaySetup)
    (hScenario : MatchesSigmaPlusDecayScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hCharges : UsesStandardParticleCharges setup)
    (hPhysical : HasPhysicalDecayParameters setup)
    (hUniformField : IsUniformMagneticFieldOutOfPage setup)
    (hCurvature : SatisfiesChargedTrackCurvatureLaw setup)
    (hConservation : SatisfiesDecayMomentumConservation setup) :
    IsClosestDisplayedMomentumChoice setup .D := by
  have hSigmaMomentum :
      momentumMagnitudeInKilogramMetersPerSecond
          (setup.momentumAtDecay .sigmaPlus) =
        (1602176634 / 10 ^ 28 : ℝ) * (23 / 20) * (199 / 100) := by
    rw [hCurvature.sigmaMomentumFromCurvature,
      hCharges.sigmaChargeMagnitudeCoulombs,
      hReadouts.magneticFieldTeslaReadout,
      hReadouts.sigmaRadiusMeterReadout]
  have hPionMomentum :
      momentumMagnitudeInKilogramMetersPerSecond
          (setup.momentumAtDecay .pionPlus) =
        (1602176634 / 10 ^ 28 : ℝ) * (23 / 20) * (29 / 50) := by
    rw [hCurvature.pionMomentumFromCurvature,
      hCharges.pionChargeMagnitudeCoulombs,
      hReadouts.magneticFieldTeslaReadout,
      hReadouts.pionRadiusMeterReadout]
  have hCosineBounds :
      (6 / 25 : ℝ) ≤ Real.cos (43 * Real.pi / 120) ∧
        Real.cos (43 * Real.pi / 120) ≤ (3 / 5 : ℝ) := by
    have hpiLower : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have hpiUpper : Real.pi ≤ 4 := Real.pi_le_four
    let x : ℝ := 17 * Real.pi / 120
    have hxNonneg : 0 ≤ x := by
      dsimp [x]
      positivity
    have hxLower : (17 / 60 : ℝ) ≤ x := by
      dsimp [x]
      nlinarith
    have hxUpper : x ≤ (17 / 30 : ℝ) := by
      dsimp [x]
      nlinarith
    have hxOne : |x| ≤ 1 := by
      rw [abs_of_nonneg hxNonneg]
      linarith
    have hSin := Real.sin_bound hxOne
    rw [abs_of_nonneg hxNonneg] at hSin
    rcases (abs_sub_le_iff.mp hSin) with ⟨hSinUpper, hSinLower⟩
    have hxCube : x ^ 3 ≤ (17 / 30 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hxNonneg hxUpper 3
    have hxFourth : x ^ 4 ≤ (17 / 30 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hxNonneg hxUpper 4
    have hCosSin :
        Real.cos (43 * Real.pi / 120) = Real.sin x := by
      rw [← Real.sin_pi_div_two_sub]
      congr 1
      dsimp [x]
      ring
    rw [hCosSin]
    constructor <;> nlinarith
  have hNeutronMomentumSq := neutronMomentumCosineRelation
    setup hReadouts hPhysical hConservation
  rw [hSigmaMomentum, hPionMomentum] at hNeutronMomentumSq
  have hSpeedOfLight :
      speedOfLightInMetersPerSecond = 299792458 := by
    simp [speedOfLightInMetersPerSecond]
  have hElectronVolt :
      electronVoltInJoules = (1602176634 / 10 ^ 28 : ℝ) := by
    simp [electronVoltInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
    norm_num
  have hMomentumConversion :
      momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) =
        momentumMagnitudeInKilogramMetersPerSecond
            (setup.momentumAtDecay .neutron) *
          299792458 /
          ((10 : ℝ) ^ 6 * (1602176634 / 10 ^ 28 : ℝ)) := by
    simp [momentumMagnitudeInMeVPerC, hSpeedOfLight, hElectronVolt]
  have hNeutronMomentumNonnegative :
      0 ≤ momentumMagnitudeInKilogramMetersPerSecond
        (setup.momentumAtDecay .neutron) := by
    exact norm_nonneg _
  have hConvertedMomentumNonnegative :
      0 ≤ momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) := by
    rw [hMomentumConversion]
    exact div_nonneg
      (mul_nonneg hNeutronMomentumNonnegative (by norm_num)) (by norm_num)
  have hConvertedMomentumSqLower :
      (1159 / 2 : ℝ) ^ 2 ≤
        momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) ^ 2 := by
    rw [hMomentumConversion]
    norm_num at hNeutronMomentumSq ⊢
    nlinarith [hCosineBounds.2]
  have hConvertedMomentumSqUpper :
      momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) ^ 2 ≤
        (668 : ℝ) ^ 2 := by
    rw [hMomentumConversion]
    norm_num at hNeutronMomentumSq ⊢
    nlinarith [hCosineBounds.1]
  have hConvertedMomentumLower :
      (1159 / 2 : ℝ) ≤
        momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) := by
    nlinarith
  have hConvertedMomentumUpper :
      momentumMagnitudeInMeVPerC (setup.momentumAtDecay .neutron) ≤ 668 := by
    nlinarith
  intro otherChoice
  fin_cases otherChoice
  · simp [displayedMomentumInMeVPerC]
    rw [← sq_le_sq]
    nlinarith
  · simp [displayedMomentumInMeVPerC]
    rw [← sq_le_sq]
    nlinarith
  · simp [displayedMomentumInMeVPerC]
    rw [← sq_le_sq]
    nlinarith
  · simp [displayedMomentumInMeVPerC]

end PhyXMiniProblems.ProblemPhyXMini0540
