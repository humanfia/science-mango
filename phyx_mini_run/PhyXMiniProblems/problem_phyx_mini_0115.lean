import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0115

open Dimension Filter
open scoped Topology

/-!
# Length of the image of an inclined pencil under a converging thin lens

The horizontal optical axis is oriented from the object toward the lens.  The
center `C` of the pencil is 45 cm to the left of the lens center and 15 cm
above the axis.  The endpoint order shown in the primary figure is `A`--`C`--`B`,
with the pencil rising to the right at 45 degrees.

All physical positions, lengths, and focal lengths are dimensionful.  Real
numbers below are only centimeter coordinate readouts, radian angle readouts,
or dimensionless ratios.  The two endpoints have different object distances,
so the leading paraxial image length is the planar distance between their
separately modeled points `A'` and `B'`.  A scale-dependent family separately
records exact physical image responses near the optical axis.  The thin-lens
and magnification relations below are imposed only as a limit and a
first-order little-o contract for that family, not as globally exact
finite-ray identities.
-/

/-- A signed physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- A point in the meridional plane of the lens, with dimensionful coordinates. -/
structure OpticalPlanePoint where
  /-- Signed coordinate along the horizontal optical axis. -/
  axialPosition : LengthQuantity
  /-- Signed transverse coordinate, positive above the optical axis. -/
  transversePosition : LengthQuantity

/-- Scalar axial-coordinate readout in centimeters. -/
def axialCoordinateCm (point : OpticalPlanePoint) : ℝ :=
  lengthInCentimeters point.axialPosition

/-- Scalar transverse-coordinate readout in centimeters. -/
def transverseCoordinateCm (point : OpticalPlanePoint) : ℝ :=
  lengthInCentimeters point.transversePosition

/-- Euclidean separation of two meridional-plane points, read in centimeters. -/
def planeDistanceCm (first second : OpticalPlanePoint) : ℝ :=
  Real.sqrt
    ((axialCoordinateCm second - axialCoordinateCm first) ^ 2 +
      (transverseCoordinateCm second - transverseCoordinateCm first) ^ 2)

/-- The three labels attached to the pencil in the primary figure. -/
inductive PencilPointLabel where
  | A
  | C
  | B
  deriving DecidableEq, Repr

/-- The two endpoints whose images determine the image length. -/
inductive PencilEndpoint where
  | A
  | B
  deriving DecidableEq, Repr

/-- Regard an endpoint label as its corresponding object-point label. -/
def PencilEndpoint.objectLabel : PencilEndpoint → PencilPointLabel
  | .A => .A
  | .B => .B

/-- Optical classification of a thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Lens silhouette recorded by the primary figure. -/
inductive LensProfile where
  | convex
  | other
  deriving DecidableEq, Repr

/-- Approximation regime selected for geometrical imaging. -/
inductive OpticalApproximation where
  | paraxial
  | nonparaxial
  deriving DecidableEq, Repr

/--
The pictured lens and its dimensional data.

`minimumDiameterForUnvignettedParaxialImage` is the aperture threshold needed
for the whole inclined pencil in the selected paraxial ray model.  The problem
does not provide a numerical aperture, only the statement that the actual
diameter is at least this threshold.
-/
structure ThinLens where
  center : OpticalPlanePoint
  kind : ThinLensKind
  profile : LensProfile
  focalLength : LengthQuantity
  apertureDiameter : LengthQuantity
  minimumDiameterForUnvignettedParaxialImage : LengthQuantity

/--
The labeled pencil, its leading paraxial endpoint images, an exact physical
image-response family near the optical axis, and the lens used to image it.

For `scaledPhysicalImageEndpoint endpoint scale`, the endpoint's axial object
position is held fixed while its transverse height relative to the axis is
scaled by the dimensionless parameter `scale`.  Thus `scale → 0` is the
near-axis limit.  The field itself carries no lens equation, solved image
coordinate, requested image length, or answer choice.
-/
structure TiltedPencilLensSetup where
  objectPoint : PencilPointLabel → OpticalPlanePoint
  /-- Leading-order paraxial image point of each endpoint. -/
  imageEndpoint : PencilEndpoint → OpticalPlanePoint
  /-- Exact physical image response along a dimensionless near-axis family. -/
  scaledPhysicalImageEndpoint : PencilEndpoint → ℝ → OpticalPlanePoint
  pencilLength : LengthQuantity
  inclinationRadians : ℝ
  lens : ThinLens
  approximation : OpticalApproximation

/-- Positive object distance from an object endpoint to the lens plane. -/
def objectDistanceCm (setup : TiltedPencilLensSetup)
    (endpoint : PencilEndpoint) : ℝ :=
  axialCoordinateCm setup.lens.center -
    axialCoordinateCm (setup.objectPoint endpoint.objectLabel)

/-- Leading paraxial real-image distance from the lens plane. -/
def imageDistanceCm (setup : TiltedPencilLensSetup)
    (endpoint : PencilEndpoint) : ℝ :=
  axialCoordinateCm (setup.imageEndpoint endpoint) -
    axialCoordinateCm setup.lens.center

/-- Signed object height relative to the optical axis through the lens center. -/
def objectHeightCm (setup : TiltedPencilLensSetup)
    (endpoint : PencilEndpoint) : ℝ :=
  transverseCoordinateCm (setup.objectPoint endpoint.objectLabel) -
    transverseCoordinateCm setup.lens.center

/-- Leading paraxial image-height coefficient relative to the optical axis. -/
def imageHeightCm (setup : TiltedPencilLensSetup)
    (endpoint : PencilEndpoint) : ℝ :=
  transverseCoordinateCm (setup.imageEndpoint endpoint) -
    transverseCoordinateCm setup.lens.center

/-- The requested leading paraxial image length, as a centimeter readout. -/
def imageLengthInCentimeters (setup : TiltedPencilLensSetup) : ℝ :=
  planeDistanceCm (setup.imageEndpoint .A) (setup.imageEndpoint .B)

/--
Numerical and geometric readouts supplied by the statement and primary figure:
the convex converging lens has focal length 20 cm; the 16 cm pencil has center
`C`, which is 45 cm before the lens and 15 cm above its axis; and the directed
segment `A B` is inclined at `π/4` radians.
-/
structure MatchesPencilLensFigure (setup : TiltedPencilLensSetup) : Prop where
  lens_is_converging : setup.lens.kind = .converging
  depicted_lens_is_convex : setup.lens.profile = .convex
  focal_length_readout :
    lengthInCentimeters setup.lens.focalLength = 20
  pencil_length_readout :
    lengthInCentimeters setup.pencilLength = 16
  center_object_distance_readout :
    axialCoordinateCm setup.lens.center -
        axialCoordinateCm (setup.objectPoint .C) = 45
  center_height_readout :
    transverseCoordinateCm (setup.objectPoint .C) -
        transverseCoordinateCm setup.lens.center = 15
  C_is_axial_midpoint :
    axialCoordinateCm (setup.objectPoint .C) =
      (axialCoordinateCm (setup.objectPoint .A) +
        axialCoordinateCm (setup.objectPoint .B)) / 2
  C_is_transverse_midpoint :
    transverseCoordinateCm (setup.objectPoint .C) =
      (transverseCoordinateCm (setup.objectPoint .A) +
        transverseCoordinateCm (setup.objectPoint .B)) / 2
  inclination_readout : setup.inclinationRadians = Real.pi / 4
  directed_axial_component :
    axialCoordinateCm (setup.objectPoint .B) -
        axialCoordinateCm (setup.objectPoint .A) =
      lengthInCentimeters setup.pencilLength *
        Real.cos setup.inclinationRadians
  directed_transverse_component :
    transverseCoordinateCm (setup.objectPoint .B) -
        transverseCoordinateCm (setup.objectPoint .A) =
      lengthInCentimeters setup.pencilLength *
        Real.sin setup.inclinationRadians
  endpoint_distance_is_pencil_length :
    planeDistanceCm (setup.objectPoint .A) (setup.objectPoint .B) =
      lengthInCentimeters setup.pencilLength

/--
The stated aperture assumption: the selected approximation is paraxial and
the actual positive lens diameter meets the aperture threshold for an
unvignetted image of both pencil endpoints.
-/
structure HasAdequateParaxialAperture
    (setup : TiltedPencilLensSetup) : Prop where
  approximation_is_paraxial : setup.approximation = .paraxial
  required_diameter_positive :
    0 < lengthInCentimeters
      setup.lens.minimumDiameterForUnvignettedParaxialImage
  actual_diameter_meets_threshold :
    lengthInCentimeters
        setup.lens.minimumDiameterForUnvignettedParaxialImage ≤
      lengthInCentimeters setup.lens.apertureDiameter

/-- Both object endpoints lie beyond the focal plane in the real-image branch. -/
structure HasRealEndpointImages (setup : TiltedPencilLensSetup) : Prop where
  focal_length_positive : 0 < lengthInCentimeters setup.lens.focalLength
  endpoint_beyond_focal_plane :
    ∀ endpoint,
      lengthInCentimeters setup.lens.focalLength <
        objectDistanceCm setup endpoint
  real_image_distance_positive :
    ∀ endpoint, 0 < imageDistanceCm setup endpoint

/--
A local asymptotic contract grounding the endpointwise paraxial model.

For each endpoint, the exact scale-dependent axial image response tends to the
modeled paraxial image distance as the transverse scale tends to zero.  The
Gaussian residual tends to zero in the same limit.  The exact transverse
response is on-axis at scale zero and has the modeled image height as its
derivative there.  Finally, the signed-magnification residual is little-o of
the scale, so `hᵢ p = -hₒ q` is only its leading-order consequence.

No field asserts either paraxial equation as an exact finite-scale law, and no
field states a solved endpoint coordinate or the requested image length.
-/
structure SatisfiesParaxialThinLensLaws
    (setup : TiltedPencilLensSetup) : Prop where
  exact_axial_response_tends_to_paraxial_image :
    ∀ endpoint,
      Filter.Tendsto
        (fun scale : ℝ =>
          axialCoordinateCm
              (setup.scaledPhysicalImageEndpoint endpoint scale) -
            axialCoordinateCm setup.lens.center)
        (nhds 0) (nhds (imageDistanceCm setup endpoint))
  gaussian_residual_tends_to_zero :
    ∀ endpoint,
      Filter.Tendsto
        (fun scale : ℝ =>
          let exactImageDistanceCm :=
            axialCoordinateCm
                (setup.scaledPhysicalImageEndpoint endpoint scale) -
              axialCoordinateCm setup.lens.center
          lengthInCentimeters setup.lens.focalLength *
                (objectDistanceCm setup endpoint + exactImageDistanceCm) -
              objectDistanceCm setup endpoint * exactImageDistanceCm)
        (nhds 0) (nhds 0)
  exact_transverse_response_on_axis :
    ∀ endpoint,
      transverseCoordinateCm
            (setup.scaledPhysicalImageEndpoint endpoint 0) -
          transverseCoordinateCm setup.lens.center = 0
  exact_transverse_response_has_paraxial_derivative :
    ∀ endpoint,
      HasDerivAt
        (fun scale : ℝ =>
          transverseCoordinateCm
              (setup.scaledPhysicalImageEndpoint endpoint scale) -
            transverseCoordinateCm setup.lens.center)
        (imageHeightCm setup endpoint) 0
  signed_magnification_residual_is_little_o :
    ∀ endpoint,
      Asymptotics.IsLittleO (nhds 0)
        (fun scale : ℝ =>
          let exactImageDistanceCm :=
            axialCoordinateCm
                (setup.scaledPhysicalImageEndpoint endpoint scale) -
              axialCoordinateCm setup.lens.center
          let exactImageHeightCm :=
            transverseCoordinateCm
                (setup.scaledPhysicalImageEndpoint endpoint scale) -
              transverseCoordinateCm setup.lens.center
          exactImageHeightCm * objectDistanceCm setup endpoint +
            scale * objectHeightCm setup endpoint * exactImageDistanceCm)
        (fun scale : ℝ => scale)

/-- The four displayed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Image-length readout printed beside each answer choice, in centimeters. -/
def answerImageLengthInCentimeters : AnswerChoice → ℝ
  | .A => 171 / 10
  | .B => 182 / 10
  | .C => 193 / 10
  | .D => 168 / 10

/-- Agreement with a displayed image length rounded to the nearest tenth cm. -/
def RoundsToNearestTenthCentimeter
    (actualLengthCm : ℝ) (choice : AnswerChoice) : Prop :=
  answerImageLengthInCentimeters choice - 1 / 20 ≤ actualLengthCm ∧
    actualLengthCm < answerImageLengthInCentimeters choice + 1 / 20

/-- A selected answer is strictly closer to the exact image length than every rival. -/
def IsClosestImageLengthAnswer
    (actualLengthCm : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other, other ≠ selected →
    |actualLengthCm - answerImageLengthInCentimeters selected| <
      |actualLengthCm - answerImageLengthInCentimeters other|

/--
The figure geometry fixes the endpoint object distances and heights.  In
particular, half of the pencil has axial and transverse projections
`4 √2 cm`.
-/
lemma objectEndpointReadouts_exact
    (setup : TiltedPencilLensSetup)
    (figure : MatchesPencilLensFigure setup) :
    objectDistanceCm setup .A = 45 + 4 * Real.sqrt 2 ∧
      objectDistanceCm setup .B = 45 - 4 * Real.sqrt 2 ∧
      objectHeightCm setup .A = 15 - 4 * Real.sqrt 2 ∧
      objectHeightCm setup .B = 15 + 4 * Real.sqrt 2 := by
  have axialComponent :
      axialCoordinateCm (setup.objectPoint .B) -
          axialCoordinateCm (setup.objectPoint .A) =
        8 * Real.sqrt 2 := by
    rw [figure.directed_axial_component, figure.pencil_length_readout,
      figure.inclination_readout, Real.cos_pi_div_four]
    ring
  have transverseComponent :
      transverseCoordinateCm (setup.objectPoint .B) -
          transverseCoordinateCm (setup.objectPoint .A) =
        8 * Real.sqrt 2 := by
    rw [figure.directed_transverse_component, figure.pencil_length_readout,
      figure.inclination_readout, Real.sin_pi_div_four]
    ring
  constructor
  · simp only [objectDistanceCm, PencilEndpoint.objectLabel]
    linarith [figure.center_object_distance_readout,
      figure.C_is_axial_midpoint]
  constructor
  · simp only [objectDistanceCm, PencilEndpoint.objectLabel]
    linarith [figure.center_object_distance_readout,
      figure.C_is_axial_midpoint]
  constructor
  · simp only [objectHeightCm, PencilEndpoint.objectLabel]
    linarith [figure.center_height_readout,
      figure.C_is_transverse_midpoint]
  · simp only [objectHeightCm, PencilEndpoint.objectLabel]
    linarith [figure.center_height_readout,
      figure.C_is_transverse_midpoint]

/--
Taking the near-axis limit and first derivative in the local asymptotic
contract gives the Gaussian and magnification relations for the leading
paraxial image points `A'` and `B'`.
-/
lemma imageEndpointReadouts_exact
    (setup : TiltedPencilLensSetup)
    (figure : MatchesPencilLensFigure setup)
    (physical : HasRealEndpointImages setup)
    (laws : SatisfiesParaxialThinLensLaws setup) :
    imageDistanceCm setup .A =
        (21860 - 1600 * Real.sqrt 2) / 593 ∧
      imageDistanceCm setup .B =
        (21860 + 1600 * Real.sqrt 2) / 593 ∧
      imageHeightCm setup .A =
        (-8140 + 3200 * Real.sqrt 2) / 593 ∧
      imageHeightCm setup .B =
        (-8140 - 3200 * Real.sqrt 2) / 593 := by
  rcases objectEndpointReadouts_exact setup figure with
    ⟨objectDistanceA, objectDistanceB, objectHeightA, objectHeightB⟩
  have gaussianEquation (endpoint : PencilEndpoint) :
      lengthInCentimeters setup.lens.focalLength *
            (objectDistanceCm setup endpoint + imageDistanceCm setup endpoint) -
          objectDistanceCm setup endpoint * imageDistanceCm setup endpoint = 0 := by
    let exactImageDistanceCm : ℝ → ℝ := fun scale =>
      axialCoordinateCm (setup.scaledPhysicalImageEndpoint endpoint scale) -
        axialCoordinateCm setup.lens.center
    have exactImageTends :
        Tendsto exactImageDistanceCm (nhds 0)
          (nhds (imageDistanceCm setup endpoint)) :=
      laws.exact_axial_response_tends_to_paraxial_image endpoint
    have calculatedLimit :
        Tendsto
          (fun scale =>
            lengthInCentimeters setup.lens.focalLength *
                  (objectDistanceCm setup endpoint +
                    exactImageDistanceCm scale) -
                objectDistanceCm setup endpoint * exactImageDistanceCm scale)
          (nhds 0)
          (nhds
            (lengthInCentimeters setup.lens.focalLength *
                  (objectDistanceCm setup endpoint +
                    imageDistanceCm setup endpoint) -
                objectDistanceCm setup endpoint *
                  imageDistanceCm setup endpoint)) := by
      exact
        (tendsto_const_nhds.mul
          (tendsto_const_nhds.add exactImageTends)).sub
            (tendsto_const_nhds.mul exactImageTends)
    exact tendsto_nhds_unique calculatedLimit
      (laws.gaussian_residual_tends_to_zero endpoint)
  have magnificationEquation (endpoint : PencilEndpoint) :
      imageHeightCm setup endpoint * objectDistanceCm setup endpoint +
          objectHeightCm setup endpoint * imageDistanceCm setup endpoint = 0 := by
    let exactImageDistanceCm : ℝ → ℝ := fun scale =>
      axialCoordinateCm (setup.scaledPhysicalImageEndpoint endpoint scale) -
        axialCoordinateCm setup.lens.center
    let exactImageHeightCm : ℝ → ℝ := fun scale =>
      transverseCoordinateCm
          (setup.scaledPhysicalImageEndpoint endpoint scale) -
        transverseCoordinateCm setup.lens.center
    have exactImageTends :
        Tendsto exactImageDistanceCm (nhds 0)
          (nhds (imageDistanceCm setup endpoint)) :=
      laws.exact_axial_response_tends_to_paraxial_image endpoint
    have exactImageHeightAtZero : exactImageHeightCm 0 = 0 :=
      laws.exact_transverse_response_on_axis endpoint
    have exactImageHeightDerivative :
        HasDerivAt exactImageHeightCm (imageHeightCm setup endpoint) 0 :=
      laws.exact_transverse_response_has_paraxial_derivative endpoint
    have heightRemainder :
        (fun scale =>
            exactImageHeightCm scale -
              scale * imageHeightCm setup endpoint) =o[nhds 0]
          (fun scale : ℝ => scale) := by
      simpa [exactImageHeightAtZero] using exactImageHeightDerivative.isLittleO
    have distanceRemainder :
        (fun scale =>
            exactImageDistanceCm scale - imageDistanceCm setup endpoint) =o[nhds 0]
          (fun _scale : ℝ => (1 : ℝ)) := by
      have constantImageDistanceTends :
          Tendsto
            (fun _scale : ℝ => imageDistanceCm setup endpoint)
            (nhds 0) (nhds (imageDistanceCm setup endpoint)) :=
        tendsto_const_nhds
      exact (Asymptotics.isLittleO_one_iff ℝ).2
        (by simpa using exactImageTends.sub constantImageDistanceTends)
    have heightContribution :
        (fun scale =>
            exactImageHeightCm scale * objectDistanceCm setup endpoint -
              scale *
                (imageHeightCm setup endpoint *
                  objectDistanceCm setup endpoint)) =o[nhds 0]
          (fun scale : ℝ => scale) := by
      exact
        (heightRemainder.const_mul_left
          (objectDistanceCm setup endpoint)).congr_left (fun scale => by ring)
    have distanceContribution :
        (fun scale =>
            scale * objectHeightCm setup endpoint *
                exactImageDistanceCm scale -
              scale *
                (objectHeightCm setup endpoint *
                  imageDistanceCm setup endpoint)) =o[nhds 0]
          (fun scale : ℝ => scale) := by
      have productRemainder :=
        (Asymptotics.isBigO_refl
          (fun scale : ℝ => scale) (nhds 0)).mul_isLittleO
          distanceRemainder
      have scaledRemainder :
          (fun scale =>
              scale *
                (exactImageDistanceCm scale -
                  imageDistanceCm setup endpoint)) =o[nhds 0]
            (fun scale : ℝ => scale) := by
        exact productRemainder.congr_right (fun scale => by ring)
      exact
        (scaledRemainder.const_mul_left
          (objectHeightCm setup endpoint)).congr_left (fun scale => by ring)
    have residualDerivativeRemainder :
        (fun scale =>
            (exactImageHeightCm scale * objectDistanceCm setup endpoint +
                scale * objectHeightCm setup endpoint *
                  exactImageDistanceCm scale) -
              scale *
                (imageHeightCm setup endpoint *
                    objectDistanceCm setup endpoint +
                  objectHeightCm setup endpoint *
                    imageDistanceCm setup endpoint)) =o[nhds 0]
          (fun scale : ℝ => scale) := by
      exact
        (heightContribution.add distanceContribution).congr_left
          (fun scale => by ring)
    have linearRemainder :
        (fun scale =>
            scale *
              (imageHeightCm setup endpoint *
                  objectDistanceCm setup endpoint +
                objectHeightCm setup endpoint *
                  imageDistanceCm setup endpoint)) =o[nhds 0]
          (fun scale : ℝ => scale) :=
      residualDerivativeRemainder.congr_of_sub.mp
        (laws.signed_magnification_residual_is_little_o endpoint)
    by_contra coefficientNonzero
    have identityIsLittleO :
        (fun scale : ℝ => scale) =o[nhds 0] (fun scale : ℝ => scale) := by
      rw [← Asymptotics.isLittleO_const_mul_left_iff coefficientNonzero]
      exact linearRemainder.congr_left (fun scale => by ring)
    have frequentlyNonzero : ∃ᶠ scale in nhds (0 : ℝ), scale ≠ 0 := by
      rw [frequently_iff_neBot]
      change Filter.NeBot (nhdsWithin 0 {0}ᶜ)
      exact inferInstance
    exact (Asymptotics.isLittleO_irrefl frequentlyNonzero) identityIsLittleO
  have sqrtTwoSquared : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have gaussianA := gaussianEquation .A
  have gaussianB := gaussianEquation .B
  rw [figure.focal_length_readout, objectDistanceA] at gaussianA
  rw [figure.focal_length_readout, objectDistanceB] at gaussianB
  have objectDistanceAAboveFocal :=
    physical.endpoint_beyond_focal_plane .A
  have objectDistanceBAboveFocal :=
    physical.endpoint_beyond_focal_plane .B
  rw [figure.focal_length_readout, objectDistanceA] at objectDistanceAAboveFocal
  rw [figure.focal_length_readout, objectDistanceB] at objectDistanceBAboveFocal
  have imageDistanceA :
      imageDistanceCm setup .A =
        (21860 - 1600 * Real.sqrt 2) / 593 := by
    nlinarith
  have imageDistanceB :
      imageDistanceCm setup .B =
        (21860 + 1600 * Real.sqrt 2) / 593 := by
    nlinarith
  have magnificationA := magnificationEquation .A
  have magnificationB := magnificationEquation .B
  rw [objectDistanceA, objectHeightA, imageDistanceA] at magnificationA
  rw [objectDistanceB, objectHeightB, imageDistanceB] at magnificationB
  have imageHeightA :
      imageHeightCm setup .A =
        (-8140 + 3200 * Real.sqrt 2) / 593 := by
    nlinarith
  have imageHeightB :
      imageHeightCm setup .B =
        (-8140 - 3200 * Real.sqrt 2) / 593 := by
    nlinarith
  exact ⟨imageDistanceA, imageDistanceB, imageHeightA, imageHeightB⟩

/-- The leading paraxial endpoint separation is `3200 √10 / 593 cm`. -/
lemma imageLengthInCentimeters_exact
    (setup : TiltedPencilLensSetup)
    (figure : MatchesPencilLensFigure setup)
    (physical : HasRealEndpointImages setup)
    (laws : SatisfiesParaxialThinLensLaws setup) :
    imageLengthInCentimeters setup =
      3200 * Real.sqrt 10 / 593 := by
  rcases imageEndpointReadouts_exact setup figure physical laws with
    ⟨imageDistanceA, imageDistanceB, imageHeightA, imageHeightB⟩
  have axialImageDifference :
      axialCoordinateCm (setup.imageEndpoint .B) -
          axialCoordinateCm (setup.imageEndpoint .A) =
        3200 * Real.sqrt 2 / 593 := by
    simp only [imageDistanceCm] at imageDistanceA imageDistanceB
    linarith
  have transverseImageDifference :
      transverseCoordinateCm (setup.imageEndpoint .B) -
          transverseCoordinateCm (setup.imageEndpoint .A) =
        -6400 * Real.sqrt 2 / 593 := by
    simp only [imageHeightCm] at imageHeightA imageHeightB
    linarith
  rw [imageLengthInCentimeters, planeDistanceCm, axialImageDifference,
    transverseImageDifference]
  have sqrtTwoSquared : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [show
      (3200 * Real.sqrt 2 / 593) ^ 2 +
          (-6400 * Real.sqrt 2 / 593) ^ 2 =
        ((3200 : ℝ) / 593) ^ 2 * 10 by
      nlinarith]
  rw [Real.sqrt_mul (sq_nonneg ((3200 : ℝ) / 593)),
    Real.sqrt_sq (by norm_num : 0 ≤ (3200 : ℝ) / 593)]
  ring

/--
The leading paraxial image has length `3200 √10 / 593 cm`, approximately
`17.1 cm` to the nearest tenth.  This uniquely selects answer A.  The exact
finite-ray response is not identified with this value; the source supplies
only the validity of the paraxial approximation, not a numerical error bound.

This formalizes `thm:physics:phyx_mini_0115:target`.
-/
theorem problem_phyx_mini_0115
    (setup : TiltedPencilLensSetup)
    (figure : MatchesPencilLensFigure setup)
    (aperture : HasAdequateParaxialAperture setup)
    (physical : HasRealEndpointImages setup)
    (laws : SatisfiesParaxialThinLensLaws setup) :
    imageLengthInCentimeters setup = 3200 * Real.sqrt 10 / 593 ∧
      RoundsToNearestTenthCentimeter
        (imageLengthInCentimeters setup) .A ∧
      IsClosestImageLengthAnswer (imageLengthInCentimeters setup) .A := by
  have exactLength :=
    imageLengthInCentimeters_exact setup figure physical laws
  refine ⟨exactLength, ?_⟩
  rw [exactLength]
  have sqrtTenSquared : (Real.sqrt 10) ^ 2 = 10 :=
    Real.sq_sqrt (by norm_num)
  have sqrtTenNonnegative : 0 ≤ Real.sqrt 10 :=
    Real.sqrt_nonneg 10
  have lengthAboveLowerChoiceBoundary :
      (341 : ℝ) / 20 < 3200 * Real.sqrt 10 / 593 := by
    nlinarith
  have lengthBelowChoiceA :
      3200 * Real.sqrt 10 / 593 < (171 : ℝ) / 10 := by
    nlinarith
  constructor
  · change
      (171 : ℝ) / 10 - 1 / 20 ≤ 3200 * Real.sqrt 10 / 593 ∧
        3200 * Real.sqrt 10 / 593 < (171 : ℝ) / 10 + 1 / 20
    constructor <;> nlinarith
  · intro other otherNotA
    cases other with
    | A => contradiction
    | B =>
        simp only [answerImageLengthInCentimeters]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        norm_num
    | C =>
        simp only [answerImageLengthInCentimeters]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        norm_num
    | D =>
        simp only [answerImageLengthInCentimeters]
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        linarith

end PhyXMiniProblems.ProblemPhyXMini0115
