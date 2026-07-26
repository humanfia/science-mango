import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0235

/-!
# Spring--solid-disk-pulley oscillator

The real-valued fields below are explicitly SI scalar readouts, rather than
definitions of the underlying physical dimensions.  The system is a family
indexed by the unspecified pulley-mass readout `M`.  Its small-oscillation mode
is represented by PhysLean's `ClassicalMechanics.HarmonicOscillator`.
-/

/-- The pictured pulley before and after its radius is doubled. -/
inductive RadiusStage where
  | original
  | doubled
  deriving DecidableEq, Repr

/-- The two straight string segments meeting at the pulley. -/
inductive StringSegment where
  | springToPulley
  | pulleyToHangingObject
  deriving DecidableEq, Repr

/-- The horizontal and vertical orientations visible in the figure. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical objects identifiable in the supplied figure. -/
inductive FigureObject where
  | wall
  | spring
  | string
  | pulleyDisk
  | axle
  | supportSurface
  | hangingObject
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the supplied figure. -/
inductive FigureLabel where
  | springConstant_k
  | pulleyMass_M
  | pulleyRadius_R
  | hangingMass_m
  deriving DecidableEq, Repr

/-- Whether a light mechanical component is idealized as massless. -/
inductive MassIdealization where
  | massless
  | massive
  deriving DecidableEq, Repr

/-- The pulley-shape alternatives relevant to rotational inertia. -/
inductive PulleyShape where
  | solidDisk
  | thinHoop
  | other
  deriving DecidableEq, Repr

/-- Axle conditions distinguished by the presence of dissipative torque. -/
inductive AxleCondition where
  | fixedSmooth
  | fixedWithFriction
  deriving DecidableEq, Repr

/-- Whether the pulley is free to rotate about its axle. -/
inductive PulleyFreedom where
  | freeToTurn
  | locked
  deriving DecidableEq, Repr

/-- Contact conditions between the string and pulley rim. -/
inductive StringPulleyContact where
  | noSlip
  | slips
  deriving DecidableEq, Repr

/-- Regimes for the displacement from static equilibrium. -/
inductive OscillationRegime where
  | smallAboutEquilibrium
  | finiteAmplitude
  deriving DecidableEq, Repr

/-- How the hanging object is prepared for the motion. -/
inductive ReleaseProtocol where
  | pulledDownAndReleased
  | externallyDriven
  deriving DecidableEq, Repr

/-- Qualitative evidence read directly from the primary image. -/
structure SpringPulleyFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  labelRefersTo : FigureLabel → FigureObject
  springOrientation : Orientation
  stringOrientation : StringSegment → Orientation
  springAttachedToWall : Bool
  springJoinedToString : Bool
  stringPassesOverPulley : Bool
  hangingObjectAttachedToString : Bool
  hangingObjectBelowPulley : Bool
  springLeftOfPulley : Bool
  radiusArrowShown : Bool

/-!
The family of spring--pulley experiments as the unspecified pulley mass `M`
varies.  Every real field ending in a unit suffix is a scalar readout in that
unit.  In particular, no physical primitive is identified with `ℝ` by an
alias.  The velocity fields preserve the stated no-slip kinematics, even
though the final extremal value depends only on the effective oscillator.
-/
structure SpringPulleyOscillator where
  springConstant_N_per_m : ℝ
  hangingMass_kg : ℝ
  gravitationalAcceleration_m_per_s2 : ℝ
  equilibriumExtension_m : ℝ
  pulleyRadius_m : RadiusStage → ℝ
  pulleyMomentOfInertia_kg_m2 : ℝ → RadiusStage → ℝ
  effectiveOscillator :
    ℝ → RadiusStage → ClassicalMechanics.HarmonicOscillator
  stringVelocity_m_per_s : ℝ → RadiusStage → ℝ → ℝ
  pulleyAngularVelocity_rad_per_s : ℝ → RadiusStage → ℝ → ℝ
  springMassIdealization : MassIdealization
  stringMassIdealization : MassIdealization
  pulleyShape : PulleyShape
  axleCondition : AxleCondition
  pulleyFreedom : PulleyFreedom
  stringPulleyContact : StringPulleyContact
  oscillationRegime : OscillationRegime
  releaseProtocol : ReleaseProtocol
  figure : SpringPulleyFigure

/-- The numerical readouts stated in the problem, all converted to SI. -/
structure MatchesProblemReadouts (setup : SpringPulleyOscillator) : Prop where
  springConstant : setup.springConstant_N_per_m = 100
  hangingMass : setup.hangingMass_kg = 200 / 1000
  originalRadius : setup.pulleyRadius_m .original = 2 / 100
  doubledRadius : setup.pulleyRadius_m .doubled = 4 / 100

/-!
The prose assumptions and primary-image incidences.  In particular, the image
shows that `M` labels the pulley disk and `R` labels its radius; it does not
show a separate block of mass `M`.
-/
def MatchesScenarioAndSuppliedFigure
    (setup : SpringPulleyOscillator) : Prop :=
  setup.springMassIdealization = .massless ∧
    setup.stringMassIdealization = .massless ∧
    setup.pulleyShape = .solidDisk ∧
    setup.axleCondition = .fixedSmooth ∧
    setup.pulleyFreedom = .freeToTurn ∧
    setup.stringPulleyContact = .noSlip ∧
    setup.oscillationRegime = .smallAboutEquilibrium ∧
    setup.releaseProtocol = .pulledDownAndReleased ∧
    (∀ object : FigureObject, setup.figure.showsObject object = true) ∧
    (∀ label : FigureLabel, setup.figure.showsLabel label = true) ∧
    setup.figure.labelRefersTo .springConstant_k = .spring ∧
    setup.figure.labelRefersTo .pulleyMass_M = .pulleyDisk ∧
    setup.figure.labelRefersTo .pulleyRadius_R = .pulleyDisk ∧
    setup.figure.labelRefersTo .hangingMass_m = .hangingObject ∧
    setup.figure.springOrientation = .horizontal ∧
    setup.figure.stringOrientation .springToPulley = .horizontal ∧
    setup.figure.stringOrientation .pulleyToHangingObject = .vertical ∧
    setup.figure.springAttachedToWall = true ∧
    setup.figure.springJoinedToString = true ∧
    setup.figure.stringPassesOverPulley = true ∧
    setup.figure.hangingObjectAttachedToString = true ∧
    setup.figure.hangingObjectBelowPulley = true ∧
    setup.figure.springLeftOfPulley = true ∧
    setup.figure.radiusArrowShown = true

/-- Positivity and nondegeneracy conditions for the physical readouts. -/
def HasPhysicalParameters (setup : SpringPulleyOscillator) : Prop :=
  0 < setup.springConstant_N_per_m ∧
    0 < setup.hangingMass_kg ∧
    0 < setup.gravitationalAcceleration_m_per_s2 ∧
    0 < setup.equilibriumExtension_m ∧
    ∀ stage : RadiusStage, 0 < setup.pulleyRadius_m stage

/-- The stated modification makes the second pulley radius twice the first. -/
structure SatisfiesRadiusDoubling
    (setup : SpringPulleyOscillator) : Prop where
  radiusLaw :
    setup.pulleyRadius_m .doubled =
      2 * setup.pulleyRadius_m .original

/-!
At the undisplaced equilibrium, the spring force balances the hanging
object's weight.  Gravity therefore fixes the equilibrium extension, though
it cancels from the linearized angular frequency.
-/
structure SatisfiesStaticEquilibrium
    (setup : SpringPulleyOscillator) : Prop where
  forceBalance :
    setup.springConstant_N_per_m * setup.equilibriumExtension_m =
      setup.hangingMass_kg * setup.gravitationalAcceleration_m_per_s2

/-- The no-slip rim relation `v = R Ω` for every modeled trajectory. -/
structure SatisfiesNoSlipKinematics
    (setup : SpringPulleyOscillator) : Prop where
  rimVelocity : ∀ (pulleyMass_kg : ℝ), 0 ≤ pulleyMass_kg →
    ∀ (stage : RadiusStage) (time_s : ℝ),
      setup.stringVelocity_m_per_s pulleyMass_kg stage time_s =
        setup.pulleyRadius_m stage *
          setup.pulleyAngularVelocity_rad_per_s pulleyMass_kg stage time_s

/-- The solid-disk moment-of-inertia law `I = (1/2) M R²`. -/
structure SatisfiesSolidDiskMomentOfInertia
    (setup : SpringPulleyOscillator) : Prop where
  inertiaLaw : ∀ (pulleyMass_kg : ℝ), 0 ≤ pulleyMass_kg →
    ∀ stage : RadiusStage,
      setup.pulleyMomentOfInertia_kg_m2 pulleyMass_kg stage =
        (1 / 2 : ℝ) * pulleyMass_kg * setup.pulleyRadius_m stage ^ 2

/-!
The Newton--Euler reduction for a light, inextensible, non-slipping string on
a smooth fixed axle.  The pulley contributes the translating effective mass
`I/R²`; the resulting one-dimensional mode has the original spring constant.
This is a governing small-oscillation law, not the requested extremal value.
-/
structure SatisfiesSmallOscillationReduction
    (setup : SpringPulleyOscillator) : Prop where
  effectiveMass : ∀ (pulleyMass_kg : ℝ), 0 ≤ pulleyMass_kg →
    ∀ stage : RadiusStage,
      (setup.effectiveOscillator pulleyMass_kg stage).m =
        setup.hangingMass_kg +
          setup.pulleyMomentOfInertia_kg_m2 pulleyMass_kg stage /
            setup.pulleyRadius_m stage ^ 2
  springConstant : ∀ (pulleyMass_kg : ℝ), 0 ≤ pulleyMass_kg →
    ∀ stage : RadiusStage,
      (setup.effectiveOscillator pulleyMass_kg stage).k =
        setup.springConstant_N_per_m

/-!
For a solid disk, `I/R² = M/2`; hence the radius cancels from the rotational
contribution to the effective translating mass.
-/
lemma solidDisk_effectiveRotationalMass
    (setup : SpringPulleyOscillator)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesSolidDiskMomentOfInertia setup)
    (pulleyMass_kg : ℝ) (hPulleyMass : 0 ≤ pulleyMass_kg)
    (stage : RadiusStage) :
    setup.pulleyMomentOfInertia_kg_m2 pulleyMass_kg stage /
        setup.pulleyRadius_m stage ^ 2 =
      pulleyMass_kg / 2 := by
  have hRadiusPos : 0 < setup.pulleyRadius_m stage :=
    hPhysical.2.2.2.2 stage
  have hRadiusSq :
      setup.pulleyRadius_m stage ^ 2 ≠ 0 :=
    pow_ne_zero 2 hRadiusPos.ne'
  rw [hInertia.inertiaLaw pulleyMass_kg hPulleyMass stage]
  field_simp [hRadiusSq]

/-!
The effective PhysLean oscillator obeys
`ω² = k / (m + M/2)` at either radius stage.
-/
lemma angularFrequency_squared
    (setup : SpringPulleyOscillator)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesSolidDiskMomentOfInertia setup)
    (hReduction : SatisfiesSmallOscillationReduction setup)
    (pulleyMass_kg : ℝ) (hPulleyMass : 0 ≤ pulleyMass_kg)
    (stage : RadiusStage) :
    (setup.effectiveOscillator pulleyMass_kg stage).ω ^ 2 =
      setup.springConstant_N_per_m /
        (setup.hangingMass_kg + pulleyMass_kg / 2) := by
  rw [ClassicalMechanics.HarmonicOscillator.ω_sq,
    hReduction.springConstant pulleyMass_kg hPulleyMass stage,
    hReduction.effectiveMass pulleyMass_kg hPulleyMass stage,
    solidDisk_effectiveRotationalMass setup hPhysical hInertia
      pulleyMass_kg hPulleyMass stage]

/-- Doubling the radius of the same solid disk does not change `ω`. -/
lemma angularFrequency_independent_of_radiusDoubling
    (setup : SpringPulleyOscillator)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesSolidDiskMomentOfInertia setup)
    (hReduction : SatisfiesSmallOscillationReduction setup)
    (pulleyMass_kg : ℝ) (hPulleyMass : 0 ≤ pulleyMass_kg) :
    (setup.effectiveOscillator pulleyMass_kg .original).ω =
      (setup.effectiveOscillator pulleyMass_kg .doubled).ω := by
  have hOriginalSq := angularFrequency_squared setup hPhysical hInertia hReduction
    pulleyMass_kg hPulleyMass .original
  have hDoubledSq := angularFrequency_squared setup hPhysical hInertia hReduction
    pulleyMass_kg hPulleyMass .doubled
  have hOriginalPos :
      0 < (setup.effectiveOscillator pulleyMass_kg .original).ω :=
    ClassicalMechanics.HarmonicOscillator.ω_pos _
  have hDoubledPos :
      0 < (setup.effectiveOscillator pulleyMass_kg .doubled).ω :=
    ClassicalMechanics.HarmonicOscillator.ω_pos _
  nlinarith

/-- The answer labels printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed angular-frequency readout for each choice, in radians/s. -/
def displayedAngularFrequency_rad_per_s : AnswerChoice → ℝ
  | .A => 204 / 10
  | .B => 234 / 10
  | .C => 214 / 10
  | .D => 224 / 10

/-- Dataset metadata recording the supplied answer label. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Standard rounding to the displayed precision of `0.1 rad/s`. -/
def RoundsToDisplayedTenth (value : ℝ) (choice : AnswerChoice) : Prop :=
  |value - displayedAngularFrequency_rad_per_s choice| < (1 / 20 : ℝ)

/-- A choice is strictly closer to a value than every other displayed choice. -/
def IsUniqueClosestDisplayedChoice
    (value : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |value - displayedAngularFrequency_rad_per_s choice| <
      |value - displayedAngularFrequency_rad_per_s other|

/-!
The formal target for `thm:physics:phyx_mini_0235:target`.

The unspecified pulley mass `M` ranges over strictly positive SI mass readouts.
The post-doubling frequencies therefore approach, but do not attain, the
least upper bound `√(100 / 0.2) = √500 rad/s` as `M` tends to zero.  Its
one-decimal display is `22.4 rad/s`, uniquely selecting answer D.
-/
theorem problem_phyx_mini_0235
    (setup : SpringPulleyOscillator)
    (hReadouts : MatchesProblemReadouts setup)
    (hScenario : MatchesScenarioAndSuppliedFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hRadiusDoubling : SatisfiesRadiusDoubling setup)
    (hEquilibrium : SatisfiesStaticEquilibrium setup)
    (hNoSlip : SatisfiesNoSlipKinematics setup)
    (hInertia : SatisfiesSolidDiskMomentOfInertia setup)
    (hReduction : SatisfiesSmallOscillationReduction setup) :
    IsLUB
        {value : ℝ | ∃ pulleyMass_kg : ℝ, 0 < pulleyMass_kg ∧
          value = (setup.effectiveOscillator pulleyMass_kg .doubled).ω}
        (Real.sqrt 500) ∧
      RoundsToDisplayedTenth (Real.sqrt 500) .D ∧
      IsUniqueClosestDisplayedChoice (Real.sqrt 500) .D := by
  have hSqrtSq : (Real.sqrt 500) ^ 2 = (500 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtNonneg : 0 ≤ Real.sqrt 500 := Real.sqrt_nonneg 500
  have hSqrtPos : 0 < Real.sqrt 500 := Real.sqrt_pos.2 (by norm_num)
  have hSqrtLower : (2235 / 100 : ℝ) < Real.sqrt 500 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtUpper : Real.sqrt 500 < (224 / 10 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  constructor
  · constructor
    · rintro value ⟨pulleyMass_kg, hPulleyMass, rfl⟩
      change
        Real.sqrt
            ((setup.effectiveOscillator pulleyMass_kg .doubled).k /
              (setup.effectiveOscillator pulleyMass_kg .doubled).m) ≤
          Real.sqrt 500
      apply Real.sqrt_le_sqrt
      rw [hReduction.springConstant pulleyMass_kg hPulleyMass.le .doubled,
        hReduction.effectiveMass pulleyMass_kg hPulleyMass.le .doubled,
        solidDisk_effectiveRotationalMass setup hPhysical hInertia
          pulleyMass_kg hPulleyMass.le .doubled,
        hReadouts.springConstant, hReadouts.hangingMass]
      have hDenominator :
          0 < (200 / 1000 : ℝ) + pulleyMass_kg / 2 := by
        norm_num
        linarith
      rw [div_le_iff₀ hDenominator]
      norm_num
      linarith
    · intro bound hBound
      have hOneMem :
          (setup.effectiveOscillator 1 .doubled).ω ∈
            {value : ℝ | ∃ pulleyMass_kg : ℝ, 0 < pulleyMass_kg ∧
              value =
                (setup.effectiveOscillator pulleyMass_kg .doubled).ω} :=
        ⟨1, by norm_num, rfl⟩
      have hOneLe :
          (setup.effectiveOscillator 1 .doubled).ω ≤ bound :=
        hBound hOneMem
      have hBoundPos : 0 < bound :=
        lt_of_lt_of_le
          (ClassicalMechanics.HarmonicOscillator.ω_pos
            (setup.effectiveOscillator 1 .doubled))
          hOneLe
      by_contra hNotUpper
      have hBoundLtSqrt : bound < Real.sqrt 500 :=
        lt_of_not_ge hNotUpper
      have hBoundSqLt : bound ^ 2 < (500 : ℝ) := by
        rw [← hSqrtSq]
        exact
          (sq_lt_sq₀ hBoundPos.le hSqrtNonneg).2 hBoundLtSqrt
      let pulleyMass_kg : ℝ := (500 - bound ^ 2) / 2500
      have hPulleyMass : 0 < pulleyMass_kg := by
        dsimp [pulleyMass_kg]
        positivity
      have hFrequencyMem :
          (setup.effectiveOscillator pulleyMass_kg .doubled).ω ∈
            {value : ℝ | ∃ pulleyMass_kg : ℝ, 0 < pulleyMass_kg ∧
              value =
                (setup.effectiveOscillator pulleyMass_kg .doubled).ω} :=
        ⟨pulleyMass_kg, hPulleyMass, rfl⟩
      have hFrequencyLe :
          (setup.effectiveOscillator pulleyMass_kg .doubled).ω ≤ bound :=
        hBound hFrequencyMem
      have hFrequencySq :=
        angularFrequency_squared setup hPhysical hInertia hReduction
          pulleyMass_kg hPulleyMass.le .doubled
      rw [hReadouts.springConstant, hReadouts.hangingMass] at hFrequencySq
      have hDenominator :
          0 < (200 / 1000 : ℝ) + pulleyMass_kg / 2 := by
        norm_num
        linarith
      have hProduct :
          0 < (500 - bound ^ 2) * (1000 - bound ^ 2) := by
        apply mul_pos <;> nlinarith
      have hBoundSqLtFrequencySq :
          bound ^ 2 <
            (100 : ℝ) / ((200 / 1000 : ℝ) + pulleyMass_kg / 2) := by
        rw [lt_div_iff₀ hDenominator]
        dsimp [pulleyMass_kg]
        nlinarith
      have hFrequencyPos :
          0 < (setup.effectiveOscillator pulleyMass_kg .doubled).ω :=
        ClassicalMechanics.HarmonicOscillator.ω_pos _
      have hFrequencySqLe :
          (setup.effectiveOscillator pulleyMass_kg .doubled).ω ^ 2 ≤
            bound ^ 2 :=
        (sq_le_sq₀ hFrequencyPos.le hBoundPos.le).2 hFrequencyLe
      nlinarith
  · constructor
    · unfold RoundsToDisplayedTenth
      simp only [displayedAngularFrequency_rad_per_s]
      rw [abs_lt]
      constructor <;> norm_num <;> linarith
    · intro other hOther
      cases other with
      | A =>
          simp only [displayedAngularFrequency_rad_per_s]
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          norm_num
          linarith
      | B =>
          simp only [displayedAngularFrequency_rad_per_s]
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          norm_num
      | C =>
          simp only [displayedAngularFrequency_rad_per_s]
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          norm_num
          linarith
      | D =>
          exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0235
