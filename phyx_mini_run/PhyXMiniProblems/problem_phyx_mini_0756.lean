import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0756

open Dimension

/-!
# Three-force equilibrium on an automobile tire

Alex, Betty, and Charles pull on a tire in the horizontal plane.  The plane
below is aligned with the supplied overhead image: coordinate `0` increases
to the right and coordinate `1` increases upward.  Thus the qualitative arrow
directions visible in the image can be retained without assigning Charles an
unreported numerical direction.

Forces are unit-independent, dimensionful planar vectors.  Bare real numbers
are used only for coherent-unit readouts, degree/radian labels, and the
displayed multiple-choice values.
-/

/-! ## Dimensionful planar forces and coherent-unit readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The image-aligned horizontal plane of the overhead tug-of-war. -/
abbrev TirePlane : Type := EuclideanSpace ℝ (Fin 2)

/-- A unit-independent physical force vector in the tire plane. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension TirePlane)

/-- Vector components of a physical force in a coherent choice of units. -/
def forceVectorReadout
    (units : UnitChoices) (force : PlanarForceQuantity) : TirePlane :=
  (force units).val

/-- Magnitude of a physical force in a coherent choice of units. -/
def forceMagnitudeReadout
    (units : UnitChoices) (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorReadout units force‖

/-- Force magnitude in SI units, hence in newtons. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  forceMagnitudeReadout UnitChoices.SI force

/-- Rightward component in the coordinate frame of the supplied image. -/
def horizontalComponent (vector : TirePlane) : ℝ := vector 0

/-- Upward component in the coordinate frame of the supplied image. -/
def verticalComponent (vector : TirePlane) : ℝ := vector 1

/-! ## Named pulls and primary-image vocabulary -/

/-- The three people whose force arrows are labelled in the image. -/
inductive Puller where
  | alex
  | betty
  | charles
  deriving DecidableEq, Fintype, Repr

/-- Named graphical elements visible in the supplied bitmap. -/
inductive FigureElement where
  | automobileTire
  | alexHand
  | bettyHand
  | charlesHand
  | alexForceArrow
  | bettyForceArrow
  | charlesForceArrow
  | alexBettyAngleArc
  | angle137DegreeLabel
  deriving DecidableEq, Fintype, Repr

/-- Presentation-level information transcribed from the supplied figure. -/
structure TugOfWarFigure where
  isShown : FigureElement → Bool
  alexBettyAngleLabelDegrees : ℝ

/-- The three physical pulls on the tire together with the supplied figure. -/
structure TireTugSetup where
  force : Puller → PlanarForceQuantity
  figure : TugOfWarFigure

/-- The undirected angle, in radians, between two physical pull vectors. -/
def pullAngleRadians
    (setup : TireTugSetup) (first second : Puller) : ℝ :=
  InnerProductGeometry.angle
    (forceVectorReadout UnitChoices.SI (setup.force first))
    (forceVectorReadout UnitChoices.SI (setup.force second))

/-! ## Stated data, figure readouts, and governing statics -/

/--
The two numerical force magnitudes stated in the prose.  Betty's requested
magnitude does not occur in this structure.
-/
structure MatchesProblemStatement (setup : TireTugSetup) : Prop where
  alexMagnitudeNewtons :
    forceMagnitudeInNewtons (setup.force .alex) = 220
  charlesMagnitudeNewtons :
    forceMagnitudeInNewtons (setup.force .charles) = 170

/--
Geometry read directly from the primary image.

The image shows Alex's arrow pointing upper-left, Betty's arrow vertically
downward, and Charles's arrow upper-right.  It labels the undirected angle
between Alex and Betty as `137°`.  The qualitative Charles quadrant is
essential: without it, the given side-angle-side data admit a second positive
Betty magnitude that is not represented by the pictured configuration.
-/
structure MatchesSuppliedFigure (setup : TireTugSetup) : Prop where
  everyNamedElementShown :
    ∀ element, setup.figure.isShown element = true
  alexBettyAngleLabelDegrees :
    setup.figure.alexBettyAngleLabelDegrees = 137
  alexBettyAngleMatchesLabel :
    pullAngleRadians setup .alex .betty =
      setup.figure.alexBettyAngleLabelDegrees * Real.pi / 180
  alexArrowPointsLeft :
    horizontalComponent
        (forceVectorReadout UnitChoices.SI (setup.force .alex)) < 0
  alexArrowPointsUp :
    0 < verticalComponent
      (forceVectorReadout UnitChoices.SI (setup.force .alex))
  bettyArrowIsVertical :
    horizontalComponent
        (forceVectorReadout UnitChoices.SI (setup.force .betty)) = 0
  bettyArrowPointsDown :
    verticalComponent
        (forceVectorReadout UnitChoices.SI (setup.force .betty)) < 0
  charlesArrowPointsRight :
    0 < horizontalComponent
      (forceVectorReadout UnitChoices.SI (setup.force .charles))
  charlesArrowPointsUp :
    0 < verticalComponent
      (forceVectorReadout UnitChoices.SI (setup.force .charles))

/--
The translational static-equilibrium law applied to the observed stationary
tire: the three horizontal force vectors have zero resultant.  This is the
governing physical relation, not the requested Betty-force magnitude.
-/
structure SatisfiesStationaryForceBalance (setup : TireTugSetup) : Prop where
  netForceIsZero :
    ∀ units,
      forceVectorReadout units (setup.force .alex) +
          forceVectorReadout units (setup.force .betty) +
        forceVectorReadout units (setup.force .charles) = 0

/-!
The equilibrium vectors form a force triangle.  Squaring the norm of
`F_C = -(F_A + F_B)` gives the cosine relation below.  This generic derived
lemma does not insert any answer choice or requested numerical magnitude.
-/
lemma stationaryForceTriangleCosineRelation
    (setup : TireTugSetup)
    (_equilibrium : SatisfiesStationaryForceBalance setup) :
    forceMagnitudeInNewtons (setup.force .charles) ^ 2 =
      forceMagnitudeInNewtons (setup.force .alex) ^ 2 +
        forceMagnitudeInNewtons (setup.force .betty) ^ 2 +
          2 * forceMagnitudeInNewtons (setup.force .alex) *
            forceMagnitudeInNewtons (setup.force .betty) *
              Real.cos (pullAngleRadians setup .alex .betty) := by
  simp only [forceMagnitudeInNewtons, forceMagnitudeReadout]
  have hbalance := _equilibrium.netForceIsZero UnitChoices.SI
  have hc : forceVectorReadout UnitChoices.SI (setup.force .charles) =
      -(forceVectorReadout UnitChoices.SI (setup.force .alex) +
        forceVectorReadout UnitChoices.SI (setup.force .betty)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc, add_left_comm, add_comm] using hbalance
  rw [hc, norm_neg, norm_add_sq_real,
    ← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
  simp only [pullAngleRadians]
  ring

/-! ## Displayed answers and final target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed force-magnitude values, in newtons. -/
def answerMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 232
  | .B => 238
  | .C => 241
  | .D => 252

/-- A displayed choice is uniquely closest to an exact force magnitude. -/
def IsClosestDisplayedAnswer
    (exactMagnitude : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |exactMagnitude - answerMagnitudeInNewtons choice| <
      |exactMagnitude - answerMagnitudeInNewtons other|

/-- An exact SI force magnitude rounds to `rounded` at the nearest newton. -/
def RoundsToNearestNewton (exactMagnitude rounded : ℝ) : Prop :=
  rounded - (1 / 2 : ℝ) ≤ exactMagnitude ∧
    exactMagnitude < rounded + (1 / 2 : ℝ)

/-!
The upper-right direction of Charles's arrow selects the larger root of the
force-triangle quadratic.  Numerically that exact root is about `240.823 N`,
so it rounds to `241 N` and makes displayed choice C uniquely closest.

Blueprint label: `thm:physics:phyx_mini_0756:target`.
-/
theorem bettyForceMagnitude
    (setup : TireTugSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedFigure setup)
    (_equilibrium : SatisfiesStationaryForceBalance setup) :
    forceMagnitudeInNewtons (setup.force .betty) =
        -((220 : ℝ) * Real.cos ((137 : ℝ) * Real.pi / 180)) +
          Real.sqrt
            ((170 : ℝ) ^ 2 -
              ((220 : ℝ) * Real.sin ((137 : ℝ) * Real.pi / 180)) ^ 2) ∧
      RoundsToNearestNewton
        (forceMagnitudeInNewtons (setup.force .betty)) 241 ∧
      IsClosestDisplayedAnswer
        (forceMagnitudeInNewtons (setup.force .betty)) .C := by
  let a : TirePlane :=
    forceVectorReadout UnitChoices.SI (setup.force .alex)
  let b : TirePlane :=
    forceVectorReadout UnitChoices.SI (setup.force .betty)
  let c : TirePlane :=
    forceVectorReadout UnitChoices.SI (setup.force .charles)
  let B : ℝ := forceMagnitudeInNewtons (setup.force .betty)
  let θ : ℝ := (137 : ℝ) * Real.pi / 180

  have haNorm : ‖a‖ = 220 := by
    simpa [a, forceMagnitudeInNewtons, forceMagnitudeReadout] using
      _problem.alexMagnitudeNewtons
  have hbNorm : ‖b‖ = B := by rfl
  have hb0 : b 0 = 0 := _figure.bettyArrowIsVertical
  have hb1neg : b 1 < 0 := _figure.bettyArrowPointsDown
  have hc1pos : 0 < c 1 := _figure.charlesArrowPointsUp
  have hangle : pullAngleRadians setup .alex .betty = θ := by
    rw [_figure.alexBettyAngleMatchesLabel,
      _figure.alexBettyAngleLabelDegrees]

  have hbsq := EuclideanSpace.real_norm_sq_eq b
  rw [hbNorm] at hbsq
  simp only [Fin.sum_univ_two, hb0] at hbsq
  have hBnonneg : 0 ≤ B := hbNorm ▸ norm_nonneg b
  have hb1eq : b 1 = -B := by nlinarith

  have hcosinner :=
    InnerProductGeometry.cos_angle_mul_norm_mul_norm a b
  change
    Real.cos (pullAngleRadians setup .alex .betty) * (‖a‖ * ‖b‖) =
      inner ℝ a b
    at hcosinner
  rw [hangle, haNorm, hbNorm, PiLp.inner_apply] at hcosinner
  simp only [Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, hb0,
    hb1eq] at hcosinner
  have hBpos : 0 < B := by nlinarith
  have ha1eq : a 1 = -220 * Real.cos θ := by nlinarith

  have hbalance := congrArg (fun v : TirePlane => v 1)
    (_equilibrium.netForceIsZero UnitChoices.SI)
  change a 1 + b 1 + c 1 = 0 at hbalance
  rw [ha1eq, hb1eq] at hbalance
  have hbranch : 0 < B + 220 * Real.cos θ := by nlinarith

  have hquad :=
    stationaryForceTriangleCosineRelation setup _equilibrium
  rw [_problem.charlesMagnitudeNewtons, _problem.alexMagnitudeNewtons,
    hangle] at hquad
  change
    170 ^ 2 =
      220 ^ 2 + B ^ 2 + 2 * 220 * B * Real.cos θ
    at hquad
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsquare :
      (B + 220 * Real.cos θ) ^ 2 =
        170 ^ 2 - (220 * Real.sin θ) ^ 2 := by
    nlinarith
  have hsqrt :
      Real.sqrt (170 ^ 2 - (220 * Real.sin θ) ^ 2) =
        B + 220 * Real.cos θ := by
    rw [← hsquare, Real.sqrt_sq (le_of_lt hbranch)]
  have hExact :
      B =
        -(220 * Real.cos θ) +
          Real.sqrt (170 ^ 2 - (220 * Real.sin θ) ^ 2) := by
    nlinarith

  clear haNorm hbNorm hb0 hb1neg hc1pos hangle hbsq hBnonneg hb1eq
    hcosinner hBpos ha1eq hbalance htrig hsquare hsqrt a b c _problem
    _figure _equilibrium

  /-
  The remaining argument gives a certified numerical enclosure.  We first
  recover `3.14 < π < 3.15` from the imported fourth-order sine estimate at
  `π / 16`, whose sine has an exact nested-radical value.
  -/
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hs2nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2L : (14142135 / 10000000 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hs2sq, hs2nonneg]
  have hs2U : Real.sqrt 2 < (14142136 / 10000000 : ℝ) := by
    nlinarith only [hs2sq, hs2nonneg]
  have hrsq :
      Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hrnonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have hrL :
      (1847759 / 1000000 : ℝ) <
        Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hrsq, hs2L, hrnonneg]
  have hrU :
      Real.sqrt (2 + Real.sqrt 2) <
        (18477591 / 10000000 : ℝ) := by
    nlinarith only [hrsq, hs2U, hrnonneg]
  have htsq :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) := by
    rw [Real.sq_sqrt]
    nlinarith only [hrU]
  have htnonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have htL :
      (390180 / 1000000 : ℝ) <
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [htsq, hrU, htnonneg]
  have htU :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
        (390181 / 1000000 : ℝ) := by
    nlinarith only [htsq, hrL, htnonneg]

  have hxpos : 0 < Real.pi / 16 := by positivity
  have hxabs : |Real.pi / 16| ≤ 1 := by
    rw [abs_of_pos hxpos]
    nlinarith [Real.pi_le_four]
  have hsinBound := Real.sin_bound hxabs
  rw [Real.sin_pi_div_sixteen, abs_of_pos hxpos] at hsinBound
  have hsinUpper := (abs_le.mp hsinBound).2
  have hpi31 : (3.1 : ℝ) < Real.pi := by
    by_contra h
    have hpile : Real.pi ≤ (3.1 : ℝ) := le_of_not_gt h
    have hxUpper : Real.pi / 16 ≤ (3.1 : ℝ) / 16 := by
      linarith
    have hx4 :
        (Real.pi / 16) ^ 4 ≤ ((3.1 : ℝ) / 16) ^ 4 := by
      gcongr
    have hx3nonneg : 0 ≤ (Real.pi / 16) ^ 3 := by
      positivity
    nlinarith only [htL, hsinUpper, hxUpper, hx4, hx3nonneg]
  have hpi313 : (3.13 : ℝ) < Real.pi := by
    by_contra h
    have hpile : Real.pi ≤ (3.13 : ℝ) := le_of_not_gt h
    have hxUpper : Real.pi / 16 ≤ (3.13 : ℝ) / 16 := by
      linarith
    have hxLower : (3.1 : ℝ) / 16 ≤ Real.pi / 16 := by
      linarith
    have hx3 :
        ((3.1 : ℝ) / 16) ^ 3 ≤ (Real.pi / 16) ^ 3 := by
      gcongr
    have hx4 :
        (Real.pi / 16) ^ 4 ≤ ((3.13 : ℝ) / 16) ^ 4 := by
      gcongr
    nlinarith only [htL, hsinUpper, hxUpper, hx3, hx4]
  have hpiL : (3.14 : ℝ) < Real.pi := by
    by_contra h
    have hpile : Real.pi ≤ (3.14 : ℝ) := le_of_not_gt h
    have hxUpper : Real.pi / 16 ≤ (3.14 : ℝ) / 16 := by
      linarith
    have hxLower : (3.13 : ℝ) / 16 ≤ Real.pi / 16 := by
      linarith
    have hx3 :
        ((3.13 : ℝ) / 16) ^ 3 ≤ (Real.pi / 16) ^ 3 := by
      gcongr
    have hx4 :
        (Real.pi / 16) ^ 4 ≤ ((3.14 : ℝ) / 16) ^ 4 := by
      gcongr
    nlinarith only [htL, hsinUpper, hxUpper, hx3, hx4]

  have hrxabs : |(3.15 : ℝ) / 16| ≤ 1 := by
    norm_num [abs_of_nonneg]
  have hsinRBound := Real.sin_bound hrxabs
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.15 / 16)]
    at hsinRBound
  have hsinRLower := (abs_le.mp hsinRBound).1
  have hpiU : Real.pi < (3.15 : ℝ) := by
    by_contra h
    have hpige : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hmono :
        Real.sin ((3.15 : ℝ) / 16) ≤ Real.sin (Real.pi / 16) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
      · linarith only [hpige]
    rw [Real.sin_pi_div_sixteen] at hmono
    nlinarith only [htU, hsinRLower, hmono]

  /-
  Write `137° = 135° + 2°`.  A small-angle sine enclosure at
  `δ = π / 90`, together with `sin² δ + cos² δ = 1`, is enough to
  enclose the required cosine to three decimal places.
  -/
  let δ : ℝ := Real.pi / 90
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδL : (3.14 : ℝ) / 90 < δ := by
    dsimp [δ]
    linarith
  have hδU : δ < (3.15 : ℝ) / 90 := by
    dsimp [δ]
    linarith
  have hδabs : |δ| ≤ 1 := by
    rw [abs_of_pos hδpos]
    linarith
  have hsinδBound := Real.sin_bound hδabs
  rw [abs_of_pos hδpos] at hsinδBound
  rcases abs_le.mp hsinδBound with
    ⟨hsinδLower, hsinδUpper⟩
  have hδ3L : ((3.14 : ℝ) / 90) ^ 3 ≤ δ ^ 3 := by
    gcongr
  have hδ3U : δ ^ 3 ≤ ((3.15 : ℝ) / 90) ^ 3 := by
    gcongr
  have hδ4U : δ ^ 4 ≤ ((3.15 : ℝ) / 90) ^ 4 := by
    gcongr
  have hsinδL : (0.0348 : ℝ) < Real.sin δ := by
    nlinarith only [hsinδLower, hδL, hδ3U, hδ4U]
  have hsinδU : Real.sin δ < (0.035 : ℝ) := by
    nlinarith only [hsinδUpper, hδU, hδ3L, hδ4U]
  have hsinδPos : 0 < Real.sin δ := by
    linarith
  have hsinδSqU :
      Real.sin δ ^ 2 < (0.035 : ℝ) ^ 2 := by
    nlinarith only [hsinδPos, hsinδU]
  have hcosδPos : 0 < Real.cos δ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith only [Real.pi_pos, hδpos]
    · dsimp [δ]
      nlinarith only [Real.pi_pos]
  have htrigδ := Real.sin_sq_add_cos_sq δ
  have hcosδL : (0.9993 : ℝ) < Real.cos δ := by
    nlinarith only [htrigδ, hsinδSqU, hcosδPos]
  have hcosδU : Real.cos δ ≤ 1 := Real.cos_le_one δ
  have hprodL :
      (0.731 : ℝ) <
        Real.sqrt 2 / 2 * (Real.cos δ + Real.sin δ) := by
    calc
      (0.731 : ℝ) <
          (1414213 / 1000000 : ℝ) / 2 * (0.9993 + 0.0348) := by
        norm_num
      _ < Real.sqrt 2 / 2 * (Real.cos δ + Real.sin δ) := by
        gcongr
        nlinarith only [hs2L, hcosδL, hsinδL]
  have hprodU :
      Real.sqrt 2 / 2 * (Real.cos δ + Real.sin δ) <
        (0.732 : ℝ) := by
    calc
      Real.sqrt 2 / 2 * (Real.cos δ + Real.sin δ) <
          (1414214 / 1000000 : ℝ) / 2 * (1 + 0.035) := by
        refine mul_lt_mul (by nlinarith only [hs2U])
          (by linarith only [hcosδU, hsinδU]) ?_ ?_
        · nlinarith only [hcosδPos, hsinδPos]
        · norm_num
      _ < (0.732 : ℝ) := by norm_num

  have hθ : θ = 3 * Real.pi / 4 + δ := by
    dsimp [θ, δ]
    ring
  have hcosθ :
      Real.cos θ =
        -(Real.sqrt 2 / 2) * (Real.cos δ + Real.sin δ) := by
    rw [hθ, Real.cos_add]
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    ring
  have hcosL : (-0.732 : ℝ) < Real.cos θ := by
    rw [hcosθ]
    nlinarith only [hprodU]
  have hcosU : Real.cos θ < (-0.731 : ℝ) := by
    rw [hcosθ]
    nlinarith only [hprodL]

  have hBLower : (240.5 : ℝ) < B := by
    nlinarith only [hquad, hbranch, hcosL, hcosU]
  have hBUpper : B < (241.5 : ℝ) := by
    nlinarith only [hquad, hbranch, hcosL, hcosU]
  have hround : RoundsToNearestNewton B 241 := by
    constructor
    · norm_num [RoundsToNearestNewton]
      linarith only [hBLower]
    · norm_num [RoundsToNearestNewton]
      linarith only [hBUpper]
  have hdistC : |B - 241| < (0.5 : ℝ) := by
    rw [abs_lt]
    constructor
    · linarith only [hBLower]
    · linarith only [hBUpper]
  have hclosest : IsClosestDisplayedAnswer B .C := by
    intro other hother
    cases other with
    | A =>
        change |B - 241| < |B - 232|
        have hr : |B - 232| = B - 232 :=
          abs_of_pos (by linarith only [hBLower])
        rw [hr]
        linarith only [hdistC, hBLower]
    | B =>
        change |B - 241| < |B - 238|
        have hr : |B - 238| = B - 238 :=
          abs_of_pos (by linarith only [hBLower])
        rw [hr]
        linarith only [hdistC, hBLower]
    | C => exact (hother rfl).elim
    | D =>
        change |B - 241| < |B - 252|
        have hr : |B - 252| = -(B - 252) :=
          abs_of_neg (by linarith only [hBUpper])
        rw [hr]
        linarith only [hdistC, hBUpper]

  refine ⟨?_, ?_, ?_⟩
  · simpa [B, θ] using hExact
  · simpa [B] using hround
  · simpa [B] using hclosest

end PhyXMiniProblems.ProblemPhyXMini0756
