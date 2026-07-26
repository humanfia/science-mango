import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0272

open Dimension

/-!
# Angular frequency of a hoop driven by a spoke-mounted spring

A thin hoop of mass `m` and outer radius `R` rotates freely about a fixed
central axle.  A horizontal spring of stiffness `k` is attached to a spoke a
distance `r` above the axle.  The supplied figure labels these three
quantities and shows a bidirectional rotation arrow below the wheel.

The model below keeps physical magnitudes as unit-independent PhysLean
quantities.  Real numbers occur only as coherent readouts, signed linearized
components, and the dimensionless angular displacement in radians.  The
small-angle laws retain the intermediate moment of inertia and restoring
torque coefficient, so the requested formula is a conclusion rather than a
field of the setup or of the governing-law interface.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for both labelled radii `r` and `R`. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/--
A linear spring constant, with dimension force per length, equivalently
`M T⁻²`.
-/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A scalar moment of inertia about the fixed axle, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
The positive coefficient `κ` in the linearized restoring torque `τ = -κ θ`.
Radians are dimensionless, so its dimension is `M L² T⁻²`.
-/
abbrev RestoringTorqueCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative angular frequency, with inverse-time dimension. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed spring extension in the tangent direction. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A signed horizontal force, with dimension `M L T⁻²`. -/
abbrev SignedForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A signed torque about the axle, with dimension `M L² T⁻²`. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical mass in a coherent choice of units. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  ((mass units).val : ℝ)

/-- Read a physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read a spring constant in coherent force-per-length units. -/
def springConstantReadout
    (units : UnitChoices) (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant units).val : ℝ)

/-- Read a moment of inertia in coherent mass-times-length-squared units. -/
def momentOfInertiaReadout
    (units : UnitChoices) (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia units).val : ℝ)

/-- Read a restoring-torque coefficient in coherent torque units per radian. -/
def restoringCoefficientReadout
    (units : UnitChoices)
    (coefficient : RestoringTorqueCoefficientQuantity) : ℝ :=
  ((coefficient units).val : ℝ)

/-- Read an angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (units : UnitChoices) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency units).val : ℝ)

/-- Read a signed tangential spring extension. -/
def signedLengthReadout
    (units : UnitChoices) (length : SignedLengthQuantity) : ℝ :=
  (length units).val

/-- Read a signed horizontal spring force. -/
def signedForceReadout
    (units : UnitChoices) (force : SignedForceQuantity) : ℝ :=
  (force units).val

/-- Read a signed torque about the fixed axle. -/
def signedTorqueReadout
    (units : UnitChoices) (torque : SignedTorqueQuantity) : ℝ :=
  (torque units).val

/-! ## Physical roles and primary-figure labels -/

/-- Physical features visible in the supplied wheel-and-spring diagram. -/
inductive FigureFeature where
  | fixedWall
  | horizontalSpring
  | wheelRim
  | spoke
  | centralAxle
  | axleToAttachmentSegment
  | axleToRimSegment
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the primary figure. -/
inductive FigureLabel where
  | springConstant_k
  | attachmentRadius_r
  | hoopRadius_R
  deriving DecidableEq, Repr

/-- Horizontal placement relative to the wheel center. -/
inductive HorizontalSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Orientation of a component or labelled segment in the equilibrium drawing. -/
inductive FigureOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Idealized distribution of the wheel's mass. -/
inductive WheelMassDistribution where
  | thinHoop
  deriving DecidableEq, Repr

/-- Mechanical constraint imposed at the central hub. -/
inductive AxleConstraint where
  | fixedInSpaceFreeToRotate
  deriving DecidableEq, Repr

/-- Approximation used for the amplitude-independent angular frequency. -/
inductive OscillationRegime where
  | linearizedSmallAngle
  deriving DecidableEq, Repr

/-- Direction information conveyed by the curved arrow below the wheel. -/
inductive RotationArrow where
  | bidirectionalAboutAxle
  deriving DecidableEq, Repr

/-!
Qualitative and labelled information transcribed from the supplied bitmap.
The image provides no numerical mass, radius, or spring-stiffness scale.
-/
structure WheelSpringFigure where
  visible : FigureFeature → Bool
  labelMarks : FigureLabel → FigureFeature
  wallSide : HorizontalSide
  springOrientation : FigureOrientation
  attachmentSegmentOrientation : FigureOrientation
  springRunsFromWallToSpoke : Bool
  attachmentPointAboveAxle : Bool
  springForceTangentialAtEquilibrium : Bool
  rotationArrow : RotationArrow

/-! ## Physical setup, figure readout, and governing assumptions -/

/-!
The independent physical quantities and linearized observables of the
wheel--spring system.  The frequency `angularFrequency_omega`, inertia, and
restoring coefficient are independent fields; none is defined to equal the
recorded answer formula.

For the signed functions, a positive angular coordinate is chosen so that
the spoke attachment moves in the positive spring-extension direction.
-/
structure HoopSpringSetup where
  figure : WheelSpringFigure
  wheelMass_m : MassQuantity
  wheelRadius_R : LengthQuantity
  attachmentRadius_r : LengthQuantity
  springConstant_k : SpringConstantQuantity
  momentOfInertiaAboutAxle : MomentOfInertiaQuantity
  linearizedRestoringCoefficient : RestoringTorqueCoefficientQuantity
  angularFrequency_omega : AngularFrequencyQuantity
  linearizedSpringExtensionAtAngleRadians : ℝ → SignedLengthQuantity
  linearizedSpringForceAtAngleRadians : ℝ → SignedForceQuantity
  linearizedSpringTorqueAtAngleRadians : ℝ → SignedTorqueQuantity
  massDistribution : WheelMassDistribution
  axleConstraint : AxleConstraint
  oscillationRegime : OscillationRegime

/-!
Problem data and primary-image evidence.  The equation `r = R` is the special
case explicitly asked for; it constrains geometry but says nothing about the
unknown angular frequency.
-/
structure MatchesProblemAndSuppliedFigure (setup : HoopSpringSetup) : Prop where
  wheelIsThinHoop : setup.massDistribution = .thinHoop
  axleIsFixedAndAllowsRotation :
    setup.axleConstraint = .fixedInSpaceFreeToRotate
  usesSmallAngleRegime : setup.oscillationRegime = .linearizedSmallAngle
  attachmentIsAtRim : setup.attachmentRadius_r = setup.wheelRadius_R
  wallVisible : setup.figure.visible .fixedWall = true
  springVisible : setup.figure.visible .horizontalSpring = true
  rimVisible : setup.figure.visible .wheelRim = true
  spokeVisible : setup.figure.visible .spoke = true
  axleVisible : setup.figure.visible .centralAxle = true
  attachmentSegmentVisible :
    setup.figure.visible .axleToAttachmentSegment = true
  radiusSegmentVisible : setup.figure.visible .axleToRimSegment = true
  kLabelsSpring :
    setup.figure.labelMarks .springConstant_k = .horizontalSpring
  rLabelsAttachmentDistance :
    setup.figure.labelMarks .attachmentRadius_r = .axleToAttachmentSegment
  RLabelsOuterRadius :
    setup.figure.labelMarks .hoopRadius_R = .axleToRimSegment
  wallIsLeftOfWheel : setup.figure.wallSide = .left
  springIsHorizontal : setup.figure.springOrientation = .horizontal
  attachmentSegmentIsVertical :
    setup.figure.attachmentSegmentOrientation = .vertical
  springConnectsWallAndSpoke : setup.figure.springRunsFromWallToSpoke = true
  attachmentIsAboveAxle : setup.figure.attachmentPointAboveAxle = true
  equilibriumSpringForceIsTangential :
    setup.figure.springForceTangentialAtEquilibrium = true
  figureShowsRotationalMotion :
    setup.figure.rotationArrow = .bidirectionalAboutAxle

/-- Strict positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalHoopSpringParameters (setup : HoopSpringSetup) : Prop where
  massPositive : ∀ units, 0 < massReadout units setup.wheelMass_m
  wheelRadiusPositive :
    ∀ units, 0 < lengthReadout units setup.wheelRadius_R
  attachmentRadiusPositive :
    ∀ units, 0 < lengthReadout units setup.attachmentRadius_r
  springConstantPositive :
    ∀ units, 0 < springConstantReadout units setup.springConstant_k
  momentOfInertiaPositive :
    ∀ units,
      0 < momentOfInertiaReadout units setup.momentOfInertiaAboutAxle
  restoringCoefficientPositive :
    ∀ units,
      0 < restoringCoefficientReadout units
        setup.linearizedRestoringCoefficient
  angularFrequencyPositive :
    ∀ units,
      0 < angularFrequencyReadout units setup.angularFrequency_omega

/-!
Governing mechanics in any coherent choice of units:

* a thin hoop has axial moment of inertia `I = m R²`;
* a small rotation `θ` moves the attachment tangentially by `x = r θ`;
* Hooke's law gives `F = -k x`, and the tangential lever arm gives `τ = r F`;
* hence the linear restoring coefficient is `κ = k r²`;
* a rotational normal mode obeys the unsimplified balance `I ω² = κ`.

The last equation is the general rotational-oscillator law.  It does not
specialize `r` to `R` and does not state the requested `sqrt (k / m)` answer.
-/
structure SatisfiesLinearizedHoopSpringLaws
    (setup : HoopSpringSetup) : Prop where
  thinHoopMomentOfInertia : ∀ units,
    momentOfInertiaReadout units setup.momentOfInertiaAboutAxle =
      massReadout units setup.wheelMass_m *
        lengthReadout units setup.wheelRadius_R ^ 2
  linearizedTangentialDisplacement : ∀ units angleRadians,
    signedLengthReadout units
        (setup.linearizedSpringExtensionAtAngleRadians angleRadians) =
      lengthReadout units setup.attachmentRadius_r * angleRadians
  hookeRestoringForce : ∀ units angleRadians,
    signedForceReadout units
        (setup.linearizedSpringForceAtAngleRadians angleRadians) =
      -(springConstantReadout units setup.springConstant_k *
        signedLengthReadout units
          (setup.linearizedSpringExtensionAtAngleRadians angleRadians))
  tangentialLeverArmTorque : ∀ units angleRadians,
    signedTorqueReadout units
        (setup.linearizedSpringTorqueAtAngleRadians angleRadians) =
      lengthReadout units setup.attachmentRadius_r *
        signedForceReadout units
          (setup.linearizedSpringForceAtAngleRadians angleRadians)
  linearizedRestoringTorque : ∀ units angleRadians,
    signedTorqueReadout units
        (setup.linearizedSpringTorqueAtAngleRadians angleRadians) =
      -(restoringCoefficientReadout units
          setup.linearizedRestoringCoefficient * angleRadians)
  restoringCoefficientFromSpring : ∀ units,
    restoringCoefficientReadout units
        setup.linearizedRestoringCoefficient =
      springConstantReadout units setup.springConstant_k *
        lengthReadout units setup.attachmentRadius_r ^ 2
  rotationalNormalModeBalance : ∀ units,
    momentOfInertiaReadout units setup.momentOfInertiaAboutAxle *
        angularFrequencyReadout units setup.angularFrequency_omega ^ 2 =
      restoringCoefficientReadout units
        setup.linearizedRestoringCoefficient

/-!
After imposing `r = R`, the radius factors cancel between `κ = k r²` and
`I = m R²`.  This intermediate squared-frequency relation is derived, not
assumed.
-/
lemma angularFrequencySquared_eq_springConstant_div_mass
    (setup : HoopSpringSetup)
    (h_problem : MatchesProblemAndSuppliedFigure setup)
    (h_physical : HasPhysicalHoopSpringParameters setup)
    (h_laws : SatisfiesLinearizedHoopSpringLaws setup) :
    ∀ units,
      angularFrequencyReadout units setup.angularFrequency_omega ^ 2 =
        springConstantReadout units setup.springConstant_k /
          massReadout units setup.wheelMass_m := by
  intro units
  have hm := h_physical.massPositive units
  have hR := h_physical.wheelRadiusPositive units
  have hI := h_laws.thinHoopMomentOfInertia units
  have hκ := h_laws.restoringCoefficientFromSpring units
  rw [h_problem.attachmentIsAtRim] at hκ
  have hbalance := h_laws.rotationalNormalModeBalance units
  rw [hI, hκ] at hbalance
  field_simp [ne_of_gt hm]
  nlinarith [sq_pos_of_pos hR]

/-! ## Displayed answer choices and formalization target -/

/-- Labels attached to the four answer choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
The four displayed angular-frequency formulas, interpreted in a coherent
choice of units.  This answer-list metadata does not constrain the independent
frequency stored in `HoopSpringSetup`.
-/
def displayedAngularFrequencyReadout
    (setup : HoopSpringSetup) (units : UnitChoices) : AnswerChoice → ℝ
  | .A =>
      Real.sqrt
        (springConstantReadout units setup.springConstant_k /
          (2 * massReadout units setup.wheelMass_m))
  | .B =>
      Real.sqrt
        ((2 * springConstantReadout units setup.springConstant_k) /
          massReadout units setup.wheelMass_m)
  | .C =>
      Real.sqrt
        (springConstantReadout units setup.springConstant_k /
          massReadout units setup.wheelMass_m)
  | .D => 0

/-- The answer label recorded by the dataset; it is not a theorem premise. -/
def recordedDatasetAnswerChoice : AnswerChoice := .C

/-- The modeled angular frequency agrees with one displayed symbolic choice. -/
def MatchesAnswerChoice
    (setup : HoopSpringSetup) (choice : AnswerChoice) : Prop :=
  ∀ units,
    angularFrequencyReadout units setup.angularFrequency_omega =
      displayedAngularFrequencyReadout setup units choice

/-!
For a spring attached at the rim (`r = R`) of a thin hoop, the small-angle
angular frequency is `ω = sqrt (k / m)`, which is displayed answer C.

This is the declaration corresponding to
`thm:physics:phyx_mini_0272:target`.
-/
theorem hoopSpringAngularFrequency_when_attachmentAtRim
    (setup : HoopSpringSetup)
    (h_problem : MatchesProblemAndSuppliedFigure setup)
    (h_physical : HasPhysicalHoopSpringParameters setup)
    (h_laws : SatisfiesLinearizedHoopSpringLaws setup) :
    (∀ units,
      angularFrequencyReadout units setup.angularFrequency_omega =
        Real.sqrt
          (springConstantReadout units setup.springConstant_k /
            massReadout units setup.wheelMass_m)) ∧
      MatchesAnswerChoice setup recordedDatasetAnswerChoice := by
  have hfrequency : ∀ units,
      angularFrequencyReadout units setup.angularFrequency_omega =
        Real.sqrt
          (springConstantReadout units setup.springConstant_k /
            massReadout units setup.wheelMass_m) := by
    intro units
    have hω := h_physical.angularFrequencyPositive units
    have hsquare :=
      angularFrequencySquared_eq_springConstant_div_mass
        setup h_problem h_physical h_laws units
    calc
      angularFrequencyReadout units setup.angularFrequency_omega =
          Real.sqrt
            (angularFrequencyReadout units setup.angularFrequency_omega ^ 2) := by
        exact (Real.sqrt_sq (le_of_lt hω)).symm
      _ = Real.sqrt
            (springConstantReadout units setup.springConstant_k /
              massReadout units setup.wheelMass_m) := by
        rw [hsquare]
  refine ⟨hfrequency, ?_⟩
  simpa [MatchesAnswerChoice, recordedDatasetAnswerChoice,
    displayedAngularFrequencyReadout] using hfrequency

end PhyXMiniProblems.ProblemPhyXMini0272
