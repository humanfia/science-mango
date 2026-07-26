import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0255

open Dimension

/-!
# Landing distance after an elastic collision with a spring-mounted block

Block 1 moves right on a frictionless elevated platform and collides
elastically with stationary block 2.  Block 2 is attached to a spring whose
effect during the short collision is negligible.  The measured period of
block 2's subsequent simple harmonic motion determines its mass.  Block 1
reverses direction, leaves the opposite edge horizontally, and falls through
the height marked `h` to a point whose horizontal distance from the platform
base is marked `d`.

Masses, lengths, durations, velocities, acceleration, and spring stiffness
are represented by Physlib dimensionful quantities.  Real numbers occur only
as coherent SI readouts, schematic figure coordinates, and displayed answer
values.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension of velocity, `L T⁻¹`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of linear spring stiffness, `M T⁻²`. -/
def springStiffnessDimension : Dimension := M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed one-dimensional physical velocity. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A nonnegative magnitude of gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical spring stiffness. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim springStiffnessDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Second readout of a physical duration. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Metre-per-second readout of a signed horizontal velocity. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  signedSIReadout velocity

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Newton-per-metre readout of a spring stiffness. -/
def stiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  nonnegativeSIReadout stiffness

/-! ## Physical roles and source-figure transcription -/

/-- The two blocks carrying the printed labels `1` and `2`. -/
inductive BlockLabel where
  | block1
  | block2
  deriving DecidableEq, Repr

/-- Horizontal directions used by the motion arrow and signed velocities. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The idealized contact condition stated for the elevated platform. -/
inductive SurfaceCondition where
  | frictionless
  deriving DecidableEq, Repr

/-- The type of collision specified in the prose. -/
inductive CollisionKind where
  | elastic
  deriving DecidableEq, Repr

/-- How strongly the attached spring acts during the short collision. -/
inductive SpringInfluenceDuringCollision where
  | negligible
  deriving DecidableEq, Repr

/-- The motion observed for block 2 after the collision. -/
inductive PostCollisionMotion where
  | simpleHarmonic
  deriving DecidableEq, Repr

/-- Physical objects and points whose relative positions are visible. -/
inductive FigureElement where
  | block1
  | block2
  | spring
  | platformDropEdge
  | rightWall
  | landingPoint
  deriving DecidableEq, Repr

/-- The three mathematical labels printed in the primary image. -/
inductive FigureQuantityLabel where
  | springConstant_k
  | dropHeight_h
  | landingDistance_d
  deriving DecidableEq, Repr

/-- Categorical and schematic-coordinate data read from the primary image. -/
structure CollisionSpringFigure where
  horizontalPosition : FigureElement → ℝ
  verticalPosition : FigureElement → ℝ
  block1MotionArrowDirection : HorizontalDirection
  springAttachedTo : BlockLabel
  springWallAnchored : Bool
  showsDashedProjectilePath : Bool
  showsLabel : FigureQuantityLabel → Bool

/-!
The physical quantities for the collision, oscillator, and subsequent fall.

The post-collision velocities, flight time, block-2 mass, and landing distance
are independent physical quantities.  Their relations are supplied only by
the governing-law premise below; in particular, the requested value of `d`
is not stored in this structure.
-/
structure ElasticCollisionSpringFallSetup where
  figure : CollisionSpringFigure
  blockMass : BlockLabel → MassQuantity
  velocityBeforeCollision : BlockLabel → VelocityQuantity
  velocityAfterCollision : BlockLabel → VelocityQuantity
  springStiffness : SpringStiffnessQuantity
  block2OscillationPeriod : TimeQuantity
  dropHeight : LengthQuantity
  landingDistance : LengthQuantity
  gravity : AccelerationQuantity
  flightTime : TimeQuantity
  block2Oscillator : ClassicalMechanics.HarmonicOscillator
  surfaceCondition : SurfaceCondition
  collisionKind : CollisionKind
  springInfluenceDuringCollision : SpringInfluenceDuringCollision
  block2PostCollisionMotion : PostCollisionMotion

/-!
Primary-image evidence: block 1 lies to the left of block 2 and initially
points right; block 2 is attached to the spring and right wall; the opposite
platform edge and landing point lie to the left.  The image also displays the
labels `k`, `h`, and `d` and a dashed projectile path.
-/
structure MatchesPrimaryFigure
    (setup : ElasticCollisionSpringFallSetup) : Prop where
  block1LeftOfBlock2 :
    setup.figure.horizontalPosition .block1 <
      setup.figure.horizontalPosition .block2
  block2LeftOfSpring :
    setup.figure.horizontalPosition .block2 <
      setup.figure.horizontalPosition .spring
  springLeftOfWall :
    setup.figure.horizontalPosition .spring <
      setup.figure.horizontalPosition .rightWall
  dropEdgeLeftOfBlock1 :
    setup.figure.horizontalPosition .platformDropEdge <
      setup.figure.horizontalPosition .block1
  landingPointLeftOfDropBase :
    setup.figure.horizontalPosition .landingPoint <
      setup.figure.horizontalPosition .platformDropEdge
  blocksAtSameElevation :
    setup.figure.verticalPosition .block1 =
      setup.figure.verticalPosition .block2
  springAtPlatformElevation :
    setup.figure.verticalPosition .spring =
      setup.figure.verticalPosition .block2
  landingPointBelowPlatform :
    setup.figure.verticalPosition .landingPoint <
      setup.figure.verticalPosition .platformDropEdge
  initialArrowPointsRight :
    setup.figure.block1MotionArrowDirection = .right
  springAttachedToBlock2 : setup.figure.springAttachedTo = .block2
  springAnchoredAtRightWall : setup.figure.springWallAnchored = true
  dashedProjectilePathShown : setup.figure.showsDashedProjectilePath = true
  springConstantLabelShown :
    setup.figure.showsLabel .springConstant_k = true
  heightLabelShown : setup.figure.showsLabel .dropHeight_h = true
  distanceLabelShown : setup.figure.showsLabel .landingDistance_d = true

/-!
Numerical readouts and qualitative conditions stated in the problem.  The
negative post-collision velocity records the prose statement that block 1
leaves from the opposite (left) end, but gives no value for that velocity or
for the landing distance.
-/
structure MatchesProblemDescription
    (setup : ElasticCollisionSpringFallSetup) : Prop where
  block1MassKilograms :
    massInKilograms (setup.blockMass .block1) = 0.200
  block1InitialVelocityMetersPerSecond :
    velocityInMetersPerSecond
        (setup.velocityBeforeCollision .block1) = 8.00
  block2InitiallyStationary :
    velocityInMetersPerSecond
        (setup.velocityBeforeCollision .block2) = 0
  springStiffnessNewtonsPerMeter :
    stiffnessInNewtonsPerMeter setup.springStiffness = 1208.5
  block2OscillationPeriodSeconds :
    timeInSeconds setup.block2OscillationPeriod = 0.140
  dropHeightMeters : lengthInMeters setup.dropHeight = 4.90
  surfaceIsFrictionless : setup.surfaceCondition = .frictionless
  collisionIsElastic : setup.collisionKind = .elastic
  springNegligibleDuringCollision :
    setup.springInfluenceDuringCollision = .negligible
  block2UndergoesSHM :
    setup.block2PostCollisionMotion = .simpleHarmonic
  block1LeavesOppositeEnd :
    velocityInMetersPerSecond
        (setup.velocityAfterCollision .block1) < 0

/-- Standard near-Earth gravitational-acceleration readout used by the model. -/
def UsesStandardNearEarthGravity
    (setup : ElasticCollisionSpringFallSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravity = 9.80

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalParameters
    (setup : ElasticCollisionSpringFallSetup) : Prop where
  block1MassPositive :
    0 < massInKilograms (setup.blockMass .block1)
  block2MassPositive :
    0 < massInKilograms (setup.blockMass .block2)
  springStiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.springStiffness
  oscillationPeriodPositive :
    0 < timeInSeconds setup.block2OscillationPeriod
  dropHeightPositive : 0 < lengthInMeters setup.dropHeight
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravity
  flightTimePositive : 0 < timeInSeconds setup.flightTime

/-! ## Governing oscillator, collision, and projectile laws -/

/-!
The ideal mechanical model consists of:

* Physlib's harmonic oscillator for block 2, whose angular frequency is
  `sqrt (k / m)` and whose period is `2 pi / omega`;
* one-dimensional momentum and kinetic-energy conservation during the
  isolated elastic collision;
* vertical constant-gravity free fall and uniform horizontal motion after
  block 1 leaves the frictionless platform.

These are general governing relations.  They contain neither the numerical
landing distance nor an answer-choice assertion.
-/
structure SatisfiesIdealMechanicalLaws
    (setup : ElasticCollisionSpringFallSetup) : Prop where
  oscillatorUsesBlock2Mass :
    setup.block2Oscillator.m =
      massInKilograms (setup.blockMass .block2)
  oscillatorUsesAttachedSpring :
    setup.block2Oscillator.k =
      stiffnessInNewtonsPerMeter setup.springStiffness
  oscillatorPeriodMatchesObservation :
    setup.block2Oscillator.period =
      timeInSeconds setup.block2OscillationPeriod
  collisionMomentumConservation :
    massInKilograms (setup.blockMass .block1) *
          velocityInMetersPerSecond
            (setup.velocityBeforeCollision .block1) +
        massInKilograms (setup.blockMass .block2) *
          velocityInMetersPerSecond
            (setup.velocityBeforeCollision .block2) =
      massInKilograms (setup.blockMass .block1) *
          velocityInMetersPerSecond
            (setup.velocityAfterCollision .block1) +
        massInKilograms (setup.blockMass .block2) *
          velocityInMetersPerSecond
            (setup.velocityAfterCollision .block2)
  collisionKineticEnergyConservation :
    (1 / 2 : ℝ) * massInKilograms (setup.blockMass .block1) *
          velocityInMetersPerSecond
              (setup.velocityBeforeCollision .block1) ^ 2 +
        (1 / 2 : ℝ) * massInKilograms (setup.blockMass .block2) *
          velocityInMetersPerSecond
              (setup.velocityBeforeCollision .block2) ^ 2 =
      (1 / 2 : ℝ) * massInKilograms (setup.blockMass .block1) *
          velocityInMetersPerSecond
              (setup.velocityAfterCollision .block1) ^ 2 +
        (1 / 2 : ℝ) * massInKilograms (setup.blockMass .block2) *
          velocityInMetersPerSecond
              (setup.velocityAfterCollision .block2) ^ 2
  verticalFreeFallLaw :
    lengthInMeters setup.dropHeight =
      (1 / 2 : ℝ) *
        accelerationInMetersPerSecondSquared setup.gravity *
          timeInSeconds setup.flightTime ^ 2
  uniformHorizontalFlightLaw :
    lengthInMeters setup.landingDistance =
      |velocityInMetersPerSecond
          (setup.velocityAfterCollision .block1)| *
        timeInSeconds setup.flightTime

/-! ## Exact readout and displayed answer choices -/

/-!
The exact SI expression obtained from the measured spring period, the
one-dimensional elastic-collision formula, and horizontal projectile motion.
This is only a scalar expression built from the stated data; the independent
physical field `setup.landingDistance` is not defined to equal it.
-/
noncomputable def exactLandingDistanceInMeters : ℝ :=
  let inferredBlock2MassKg : ℝ :=
    (1208.5 : ℝ) * ((0.140 : ℝ) / (2 * Real.pi)) ^ 2
  let block1PostCollisionVelocityMetersPerSecond : ℝ :=
    (((0.200 : ℝ) - inferredBlock2MassKg) /
        ((0.200 : ℝ) + inferredBlock2MassKg)) * 8.00
  |block1PostCollisionVelocityMetersPerSecond| *
    Real.sqrt ((2 * (4.90 : ℝ)) / (9.80 : ℝ))

/-- Labels of the four numerical choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance in metres printed beside each displayed answer choice. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 3.0
  | .B => 3.5
  | .C => 4.0
  | .D => 4.5

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement of the physical distance with a displayed nearest-tenth metre. -/
def MatchesDisplayedDistance
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters distance - choice.distanceInMeters| ≤ (1 : ℝ) / 20

/-!
The governing laws determine the exact (unrounded) landing-distance readout.
-/
lemma landingDistance_eq_exactExpression
    (setup : ElasticCollisionSpringFallSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_physical : HasPhysicalParameters setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_laws : SatisfiesIdealMechanicalLaws setup) :
    lengthInMeters setup.landingDistance =
      exactLandingDistanceInMeters := by
  set_option maxHeartbeats 800000 in
    all_goals
      let m2 : ℝ := massInKilograms (setup.blockMass .block2)
      let v1 : ℝ :=
        velocityInMetersPerSecond (setup.velocityAfterCollision .block1)
      let v2 : ℝ :=
        velocityInMetersPerSecond (setup.velocityAfterCollision .block2)
      let S : ClassicalMechanics.HarmonicOscillator := setup.block2Oscillator
      have h0200 : (0.200 : ℝ) = 1 / 5 := by norm_num
      have h12085 : (1208.5 : ℝ) = 2417 / 2 := by norm_num
      have h0140 : (0.140 : ℝ) = 7 / 50 := by norm_num
      have h800 : (8.00 : ℝ) = 8 := by norm_num
      have hsqrt : √(2 * (4.90 : ℝ) / 9.80) = 1 := by norm_num
      have hm2pos : 0 < m2 := by
        simpa [m2] using _physical.block2MassPositive
      have hSm : S.m = m2 := by
        simpa [S, m2] using _laws.oscillatorUsesBlock2Mass
      have hSk : S.k = (2417 / 2 : ℝ) := by
        calc
          S.k = stiffnessInNewtonsPerMeter setup.springStiffness := by
            simpa [S] using _laws.oscillatorUsesAttachedSpring
          _ = (2417 / 2 : ℝ) := by
            have h := _description.springStiffnessNewtonsPerMeter
            norm_num at h ⊢
            exact h
      have hperiod : S.period = (7 / 50 : ℝ) := by
        calc
          S.period = timeInSeconds setup.block2OscillationPeriod := by
            simpa [S] using _laws.oscillatorPeriodMatchesObservation
          _ = (7 / 50 : ℝ) := by
            have h := _description.block2OscillationPeriodSeconds
            norm_num at h ⊢
            exact h
      have hperiod_formula :
          2 * Real.pi / S.ω = (7 / 50 : ℝ) := by
        simpa [ClassicalMechanics.HarmonicOscillator.period_eq] using hperiod
      have homega : S.ω = 100 * Real.pi / 7 := by
        have h := (div_eq_iff S.ω_ne_zero).mp hperiod_formula
        nlinarith only [h]
      have homega_sq := S.ω_sq
      rw [hSm, hSk, homega] at homega_sq
      have hm2eq :
          m2 = (2417 / 2 : ℝ) * (7 / 50 / (2 * Real.pi)) ^ 2 := by
        field_simp [Real.pi_ne_zero, hm2pos.ne'] at homega_sq ⊢
        nlinarith only [homega_sq]
      have hv1neg : v1 < 0 := by
        simpa [v1] using _description.block1LeavesOppositeEnd
      have hmom :
          (1 / 5 : ℝ) * 8 = (1 / 5 : ℝ) * v1 + m2 * v2 := by
        have h := _laws.collisionMomentumConservation
        rw [_description.block1MassKilograms,
          _description.block1InitialVelocityMetersPerSecond,
          _description.block2InitiallyStationary] at h
        norm_num [m2, v1, v2] at h ⊢
        exact h
      have henergy :
          (1 / 2 : ℝ) * (1 / 5) * 8 ^ 2 =
            (1 / 2 : ℝ) * (1 / 5) * v1 ^ 2 +
              (1 / 2) * m2 * v2 ^ 2 := by
        have h := _laws.collisionKineticEnergyConservation
        rw [_description.block1MassKilograms,
          _description.block1InitialVelocityMetersPerSecond,
          _description.block2InitiallyStationary] at h
        norm_num [m2, v1, v2] at h ⊢
        exact h
      have hmom_mul := congrArg (fun x : ℝ => x * v2) hmom
      have hfactor : (8 - v1) * (v2 - (8 + v1)) = 0 := by
        nlinarith only [hmom_mul, henergy]
      have hv2eq : v2 = 8 + v1 := by
        rcases mul_eq_zero.mp hfactor with h | h
        · nlinarith only [h, hv1neg]
        · nlinarith only [h]
      have hden : 0 < (1 / 5 : ℝ) + m2 := by
        nlinarith only [hm2pos]
      have hmom_formula := hmom
      rw [hv2eq] at hmom_formula
      have hv1formula :
          v1 = ((1 / 5 - m2) / (1 / 5 + m2)) * 8 := by
        field_simp [hden.ne']
        nlinarith only [hmom_formula]
      have hheight := _description.dropHeightMeters
      have hgravity := _gravity
      have hfall := _laws.verticalFreeFallLaw
      have htpos := _physical.flightTimePositive
      dsimp [UsesStandardNearEarthGravity] at hgravity
      norm_num at hheight hgravity hfall
      have ht_sq : timeInSeconds setup.flightTime ^ 2 = 1 := by
        nlinarith only [hheight, hgravity, hfall]
      have ht : timeInSeconds setup.flightTime = 1 := by
        nlinarith only [ht_sq, htpos]
      rw [_laws.uniformHorizontalFlightLaw, ht]
      change abs v1 * 1 = exactLandingDistanceInMeters
      rw [hv1formula, hm2eq]
      unfold exactLandingDistanceInMeters
      set_option maxHeartbeats 800000 in
        dsimp
        rw [h0200, h12085, h0140, h800, hsqrt]

/-!
The exact expression is approximately `3.99994 m`, so it agrees with the
displayed nearest-tenth value `4.0 m`.
-/
lemma exactLandingDistance_matches_choice_C :
    |exactLandingDistanceInMeters -
        AnswerChoice.C.distanceInMeters| ≤ (1 : ℝ) / 20 := by
  have pi_gt_sqrtTwoAddSeries_local (n : ℕ) :
      2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) < Real.pi := by
    have h :
        √(2 - Real.sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply Real.sin_lt
        apply div_pos Real.pi_pos
      all_goals
        apply pow_pos
        norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) h
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have pi_lt_sqrtTwoAddSeries_local (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have h :
        Real.pi <
          (√(2 - Real.sqrtTwoAddSeries 0 n) / 2 +
              1 / (2 ^ n) ^ 3 / 4) *
            (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by simp), ← Real.sin_pi_over_two_pow_succ,
        ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <| Real.sin_gt_sub_cube (by positivity) <|
            div_le_one_of_le₀ (by
              calc
                Real.pi ≤ 4 := Real.pi_le_four
                _ = 2 ^ (0 + 2) := by norm_num
                _ ≤ 2 ^ (n + 2) := by gcongr <;> norm_num) (by positivity)
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le h (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div,
      ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc,
        mul_comm n]
    all_goals norm_num
  have sqrtTwoAddSeries_step_up_local
      (c d : ℕ) {a b n : ℕ} {z : ℝ}
      (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
      (hb : 0 < b) (hd : 0 < d)
      (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
      Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
    refine le_trans ?_ hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
      div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
      div_le_div_iff₀ hb' (pow_pos hd' _)]
    exact_mod_cast h
  have sqrtTwoAddSeries_step_down_local
      (a b : ℕ) {c d n : ℕ} {z : ℝ}
      (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
      (hb : 0 < b) (hd : 0 < d)
      (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
      z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
    apply le_trans hz
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    apply Real.le_sqrt_of_sq_le
    have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
      div_le_div_iff₀ (pow_pos hb' _) hd']
    exact_mod_cast h
  have pi_lower_bound_start_local (n : ℕ) {a : ℝ}
      (h : Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
        (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
      a < Real.pi := by
    refine lt_of_le_of_lt ?_ (pi_gt_sqrtTwoAddSeries_local n)
    rw [mul_comm]
    refine (div_le_iff₀ (pow_pos (by simp) _)).mp
      (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm,
      show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
        rw [Nat.cast_zero, zero_div]]
  have pi_upper_bound_start_local (n : ℕ) {a : ℝ}
      (h : (2 : ℝ) -
          ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
      (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
      Real.pi < a := by
    refine lt_of_lt_of_le (pi_lt_sqrtTwoAddSeries_local n) ?_
    rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left,
      sub_le_comm]
    · rwa [Nat.cast_zero, zero_div] at h
    · exact div_nonneg (sub_nonneg.2 h₂)
        (pow_nonneg (le_of_lt zero_lt_two) _)
    · exact pow_pos zero_lt_two _
  have hpi_lower : (3.14 : ℝ) < Real.pi := by
    apply pi_lower_bound_start_local 4
    refine sqrtTwoAddSeries_step_up_local 338 239 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrtTwoAddSeries_step_up_local 704 381 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrtTwoAddSeries_step_up_local 1940 989 ?_
      (by norm_num) (by norm_num) (by norm_num)
    refine sqrtTwoAddSeries_step_up_local 1447 727 ?_
      (by norm_num) (by norm_num) (by norm_num)
    simp [Real.sqrtTwoAddSeries]
    norm_num
  have hpi_upper : Real.pi < (3.15 : ℝ) := by
    apply pi_upper_bound_start_local 4
    · refine sqrtTwoAddSeries_step_down_local 41 29 ?_
        (by norm_num) (by norm_num) (by norm_num)
      refine sqrtTwoAddSeries_step_down_local 109 59 ?_
        (by norm_num) (by norm_num) (by norm_num)
      refine sqrtTwoAddSeries_step_down_local 865 441 ?_
        (by norm_num) (by norm_num) (by norm_num)
      refine sqrtTwoAddSeries_step_down_local 412 207 ?_
        (by norm_num) (by norm_num) (by norm_num)
      simp [Real.sqrtTwoAddSeries]
      norm_num
    · norm_num
  norm_num [exactLandingDistanceInMeters, AnswerChoice.distanceInMeters]
  let m : ℝ := 2417 / 2 * (7 / 50 / (2 * Real.pi)) ^ 2
  change abs (abs ((1 / 5 - m) / (1 / 5 + m)) * 8 - 4) ≤ 1 / 20
  have hpi_sq_lower : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hpi_lower)
      (by positivity : 0 < Real.pi + 3.14)]
  have hpi_sq_upper : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hpi_upper)
      (by positivity : 0 < 3.15 + Real.pi)]
  have hm_eq : m = 118433 / (20000 * Real.pi ^ 2) := by
    dsimp [m]
    field_simp [Real.pi_ne_zero]
    all_goals ring
  have hm_pos : 0 < m := by
    rw [hm_eq]
    positivity
  have hm_gt : (1 / 5 : ℝ) < m := by
    rw [hm_eq,
      lt_div_iff₀ (by positivity : 0 < 20000 * Real.pi ^ 2)]
    nlinarith
  have hden : 0 < (1 / 5 : ℝ) + m := by positivity
  have hr_nonpos : (1 / 5 - m) / (1 / 5 + m) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  have hr_eq :
      (1 / 5 - m) / (1 / 5 + m) =
        (4000 * Real.pi ^ 2 - 118433) /
          (4000 * Real.pi ^ 2 + 118433) := by
    rw [hm_eq]
    field_simp [Real.pi_ne_zero]
    all_goals ring
  let speed : ℝ :=
    8 * (118433 - 4000 * Real.pi ^ 2) /
      (118433 + 4000 * Real.pi ^ 2)
  have hspeed_eq :
      -((4000 * Real.pi ^ 2 - 118433) /
          (4000 * Real.pi ^ 2 + 118433)) * 8 = speed := by
    dsimp [speed]
    ring
  have hspeed_den_pos :
      0 < (118433 : ℝ) + 4000 * Real.pi ^ 2 := by positivity
  have hspeed_lower : (79 / 20 : ℝ) ≤ speed := by
    dsimp [speed]
    rw [le_div_iff₀ hspeed_den_pos]
    nlinarith
  have hspeed_upper : speed ≤ (81 / 20 : ℝ) := by
    dsimp [speed]
    rw [div_le_iff₀ hspeed_den_pos]
    nlinarith
  rw [abs_of_nonpos hr_nonpos, hr_eq, hspeed_eq, abs_le]
  constructor <;> linarith

/-!
The exact physical readout rounds to `4.0 m`, answer choice C.

Blueprint: `thm:physics:phyx_mini_0255:target`.
-/
theorem problem_phyx_mini_0255
    (setup : ElasticCollisionSpringFallSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_physical : HasPhysicalParameters setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_laws : SatisfiesIdealMechanicalLaws setup) :
    lengthInMeters setup.landingDistance =
        exactLandingDistanceInMeters ∧
      MatchesDisplayedDistance setup.landingDistance .C := by
  have h := landingDistance_eq_exactExpression setup _figure _description
    _physical _gravity _laws
  constructor
  · exact h
  · dsimp [MatchesDisplayedDistance]
    rw [h]
    exact exactLandingDistance_matches_choice_C

end PhyXMiniProblems.ProblemPhyXMini0255
