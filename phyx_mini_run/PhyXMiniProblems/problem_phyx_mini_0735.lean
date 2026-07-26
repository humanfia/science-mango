import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0735

open Dimension

/-!
# Strike-slip and dip-slip components of a fault displacement

The supplied figure resolves the net displacement `AB`, which lies in the
fault plane, into the horizontal strike-slip component `AC` and the down-plane
dip-slip component `AD`.  Displacements are unit-independent physical vectors;
real vectors occur only after choosing a length unit for a readout.

The recorded answer `27.8 m` is rounded to one decimal place.  The theorem
therefore retains the exact square-root magnitude and separately states the
corresponding rounding tolerance.
-/

/-! ## Dimensionful fault-plane vectors and unit readouts -/

/-- A real two-dimensional coordinate vector intrinsic to the fault plane. -/
abbrev FaultPlaneVector : Type := EuclideanSpace ℝ (Fin 2)

/-- A unit-independent physical displacement vector of length dimension. -/
abbrev DisplacementVector : Type :=
  Dimensionful (WithDim L𝓭 FaultPlaneVector)

/-- Read a physical displacement vector in a selected length unit. -/
def displacementReadout
    (unit : LengthUnit) (displacement : DisplacementVector) :
    FaultPlaneVector :=
  (displacement ({UnitChoices.SI with length := unit} : UnitChoices)).val

/-- Read a physical displacement vector in metres. -/
def displacementInMeters (displacement : DisplacementVector) :
    FaultPlaneVector :=
  displacementReadout LengthUnit.meters displacement

/-- Read the magnitude of a physical displacement in a selected length unit. -/
def displacementMagnitudeReadout
    (unit : LengthUnit) (displacement : DisplacementVector) : ℝ :=
  ‖displacementReadout unit displacement‖

/-- Read the magnitude of a physical displacement in metres. -/
def displacementMagnitudeInMeters (displacement : DisplacementVector) : ℝ :=
  displacementMagnitudeReadout LengthUnit.meters displacement

/-! ## Labels and geometry from the primary figure -/

/-- The four point labels printed on the supplied fault-plane diagram. -/
inductive FaultPoint where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The labeled segments used in the parallelogram decomposition. -/
inductive FaultSegment where
  | AB
  | AC
  | AD
  | CD
  deriving DecidableEq, Fintype, Repr

/-- The initial endpoint associated with each labeled segment. -/
def segmentStart : FaultSegment → FaultPoint
  | .AB | .AC | .AD => .A
  | .CD => .C

/-- The terminal endpoint associated with each labeled segment. -/
def segmentEnd : FaultSegment → FaultPoint
  | .AB => .B
  | .AC => .C
  | .AD => .D
  | .CD => .D

/-- Kinematic roles assigned to lines in the supplied figure. -/
inductive SegmentRole where
  | netSlip
  | strikeSlip
  | dipSlip
  | constructionLine
  deriving DecidableEq, Repr

/-- Drawing styles that distinguish the figure's arrow and construction lines. -/
inductive SegmentStyle where
  | orangeArrow
  | redComponent
  | dashedConstruction
  deriving DecidableEq, Repr

/-!
The physical vectors and auxiliary annotations displayed in image 735.  The
dip angle `phi` is dimensionless and is represented by its radian readout.
-/
structure FaultPlaneFigure where
  segmentVector : FaultSegment → DisplacementVector
  segmentRole : FaultSegment → SegmentRole
  segmentStyle : FaultSegment → SegmentStyle
  pointOnFaultPlane : FaultPoint → Bool
  coincidedBeforeSlip : FaultPoint → FaultPoint → Bool
  dashedConstructionPassesThroughB : Bool
  rightAngleMarkerShown : Bool
  faultPlaneLabelShown : Bool
  foregroundMotionShownDownAndRight : Bool
  dipAnglePhiRadians : ℝ

/-!
Evidence read from the primary raster and the scenario text.  These fields
record labels, line styles, qualitative motion, and the acute angle `phi`; they
do not constrain the requested net magnitude.
-/
structure MatchesPrimaryFigure (figure : FaultPlaneFigure) : Prop where
  allLabeledPointsLieOnFaultPlane :
    ∀ point : FaultPoint, figure.pointOnFaultPlane point = true
  pointsAandBCoincidedBeforeSlip :
    figure.coincidedBeforeSlip .A .B = true
  abIsNetSlip : figure.segmentRole .AB = .netSlip
  acIsHorizontalStrikeSlip : figure.segmentRole .AC = .strikeSlip
  adIsDownPlaneDipSlip : figure.segmentRole .AD = .dipSlip
  cdIsConstructionLine : figure.segmentRole .CD = .constructionLine
  abIsOrangeArrow : figure.segmentStyle .AB = .orangeArrow
  acAndAdAreRedComponents :
    figure.segmentStyle .AC = .redComponent ∧
      figure.segmentStyle .AD = .redComponent
  cdIsDashed : figure.segmentStyle .CD = .dashedConstruction
  dashedLinePassesThroughB :
    figure.dashedConstructionPassesThroughB = true
  rightAngleIsMarked : figure.rightAngleMarkerShown = true
  faultPlaneIsLabeled : figure.faultPlaneLabelShown = true
  foregroundMovesDownAndRight :
    figure.foregroundMotionShownDownAndRight = true
  phiIsAcute :
    0 < figure.dipAnglePhiRadians ∧
      figure.dipAnglePhiRadians < Real.pi / 2

/-! ## Governing kinematics and numerical data -/

/-!
The component law for the free displacement vectors in the fault plane.
It is stated in every length unit: `AB` is the vector sum of `AC` and `AD`,
and the strike and dip directions are perpendicular.
-/
structure FaultComponentLaws (figure : FaultPlaneFigure) : Prop where
  componentDecomposition :
    ∀ unit : LengthUnit,
      displacementReadout unit (figure.segmentVector .AB) =
        displacementReadout unit (figure.segmentVector .AC) +
          displacementReadout unit (figure.segmentVector .AD)
  strikeDipOrthogonal :
    ∀ unit : LengthUnit,
      inner ℝ
          (displacementReadout unit (figure.segmentVector .AC))
          (displacementReadout unit (figure.segmentVector .AD)) = 0

/-!
The two measured component magnitudes supplied in the question.  No field here
mentions the net magnitude or the recorded answer choice.
-/
structure MatchesProblemData (figure : FaultPlaneFigure) : Prop where
  strikeSlipMagnitudeMeters :
    displacementMagnitudeInMeters (figure.segmentVector .AC) = 22.0
  dipSlipMagnitudeMeters :
    displacementMagnitudeInMeters (figure.segmentVector .AD) = 17.0

/-!
From the orthogonal `22.0 m` and `17.0 m` components, the net displacement has
exact magnitude `sqrt (22^2 + 17^2)` metres and is within `0.05 m` of
`27.8 m`, so its one-decimal-place report is answer choice C.
-/
theorem netDisplacementMagnitude
    (figure : FaultPlaneFigure)
    (_figureEvidence : MatchesPrimaryFigure figure)
    (_laws : FaultComponentLaws figure)
    (_data : MatchesProblemData figure) :
    displacementMagnitudeInMeters (figure.segmentVector .AB) =
        Real.sqrt ((22.0 : ℝ) ^ 2 + (17.0 : ℝ) ^ 2) ∧
      |displacementMagnitudeInMeters (figure.segmentVector .AB) - 27.8| <
        0.05 := by
  have hstrike :
      ‖displacementReadout LengthUnit.meters (figure.segmentVector .AC)‖ =
        (22.0 : ℝ) := by
    simpa [displacementMagnitudeInMeters, displacementMagnitudeReadout] using
      _data.strikeSlipMagnitudeMeters
  have hdip :
      ‖displacementReadout LengthUnit.meters (figure.segmentVector .AD)‖ =
        (17.0 : ℝ) := by
    simpa [displacementMagnitudeInMeters, displacementMagnitudeReadout] using
      _data.dipSlipMagnitudeMeters
  have hmag :
      displacementMagnitudeInMeters (figure.segmentVector .AB) =
        Real.sqrt ((22.0 : ℝ) ^ 2 + (17.0 : ℝ) ^ 2) := by
    calc
      displacementMagnitudeInMeters (figure.segmentVector .AB) =
          ‖displacementReadout LengthUnit.meters
            (figure.segmentVector .AB)‖ := rfl
      _ = ‖displacementReadout LengthUnit.meters
              (figure.segmentVector .AC) +
            displacementReadout LengthUnit.meters
              (figure.segmentVector .AD)‖ := by
        rw [_laws.componentDecomposition LengthUnit.meters]
      _ = Real.sqrt
            (‖displacementReadout LengthUnit.meters
                  (figure.segmentVector .AC)‖ *
                ‖displacementReadout LengthUnit.meters
                  (figure.segmentVector .AC)‖ +
              ‖displacementReadout LengthUnit.meters
                  (figure.segmentVector .AD)‖ *
                ‖displacementReadout LengthUnit.meters
                  (figure.segmentVector .AD)‖) :=
        norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr
          (_laws.strikeDipOrthogonal LengthUnit.meters)
      _ = Real.sqrt ((22.0 : ℝ) ^ 2 + (17.0 : ℝ) ^ 2) := by
        rw [hstrike, hdip]
        norm_num
  refine ⟨hmag, ?_⟩
  rw [hmag, abs_lt]
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((22.0 : ℝ) ^ 2 + (17.0 : ℝ) ^ 2) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      (Real.sqrt ((22.0 : ℝ) ^ 2 + (17.0 : ℝ) ^ 2)) ^ 2 =
        (22.0 : ℝ) ^ 2 + (17.0 : ℝ) ^ 2 :=
    Real.sq_sqrt (by positivity)
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0735
