import Mathlib
import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0555

/-!
# Fixed-target threshold production of an antiproton

An incident proton strikes a proton at rest in the laboratory and produces

`p + p -> p + p + p + p_bar`.

At threshold the four outgoing particles have one common velocity.  Physical
rest and kinetic energies below use Physlib's unit-independent `DimEnergy`.
Four-momenta use Physlib's real Lorentz vectors after taking calibrated
natural-unit readouts: the time component is measured in GeV and each spatial
component in GeV/`c`.  Thus the Minkowski mass-shell relation is dimensionally
homogeneous in units with `c = 1`.

Real numbers are otherwise used only for unit readouts, diagram coordinates,
and the values printed in the multiple-choice list.
-/

/-! ## Dimensionful energies and calibrated readouts -/

/-- Read a physical energy in electron-volts. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.electronVolt UnitChoices.SI).val

/-- Read a physical energy in mega-electron-volts. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInElectronVolts energy / (10 : ℝ) ^ 6

/-- Read a physical energy in giga-electron-volts. -/
def energyInGigaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInElectronVolts energy / (10 : ℝ) ^ 9

/-! ## Reaction roles and particle species -/

/-- The two particle species occurring in the reaction. -/
inductive ParticleSpecies where
  | proton
  | antiproton
  deriving DecidableEq, Repr

/-- Coarse charge sign, sufficient to record the stated opposite charges. -/
inductive ElectricChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The proton and antiproton have opposite electric-charge signs. -/
def ParticleSpecies.chargeSign : ParticleSpecies → ElectricChargeSign
  | .proton => .positive
  | .antiproton => .negative

/-- The two incoming and four outgoing particle roles in the reaction. -/
inductive ReactionParticle where
  | incidentProton
  | targetProton
  | outgoingProton₁
  | outgoingProton₂
  | outgoingProton₃
  | outgoingAntiproton
  deriving DecidableEq, Fintype, Repr

/-- Species of each individually tracked reaction particle. -/
def ReactionParticle.species : ReactionParticle → ParticleSpecies
  | .incidentProton => .proton
  | .targetProton => .proton
  | .outgoingProton₁ => .proton
  | .outgoingProton₂ => .proton
  | .outgoingProton₃ => .proton
  | .outgoingAntiproton => .antiproton

/-- Predicate selecting exactly the four particles in the final state. -/
inductive ReactionParticle.IsOutgoing : ReactionParticle → Prop where
  | proton₁ : ReactionParticle.IsOutgoing .outgoingProton₁
  | proton₂ : ReactionParticle.IsOutgoing .outgoingProton₂
  | proton₃ : ReactionParticle.IsOutgoing .outgoingProton₃
  | antiproton : ReactionParticle.IsOutgoing .outgoingAntiproton

/-! ## Labels and geometry read from the supplied two-panel figure -/

/-- Initial and threshold-final panels separated by the vertical rule. -/
inductive FigurePanel where
  | initial
  | thresholdFinal
  deriving DecidableEq, Fintype, Repr

/-- The horizontal and vertical axes drawn in each panel. -/
inductive FigureAxis where
  | xAxis
  | yAxis
  deriving DecidableEq, Fintype, Repr

/-- Horizontal orientation of a velocity arrow in the diagram. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- The two visibly different particle colors in the final cluster. -/
inductive FigureColor where
  | lightBlue
  | gray
  deriving DecidableEq, Repr

/-- One raster glyph for each particle displayed in the two panels. -/
inductive FigureParticleGlyph where
  | incidentProton
  | targetProton
  | finalProtonTop
  | finalProtonBottomLeft
  | finalProtonBottomRight
  | finalAntiproton
  deriving DecidableEq, Fintype, Repr

/-- Species represented by a particle glyph. -/
def FigureParticleGlyph.species : FigureParticleGlyph → ParticleSpecies
  | .incidentProton => .proton
  | .targetProton => .proton
  | .finalProtonTop => .proton
  | .finalProtonBottomLeft => .proton
  | .finalProtonBottomRight => .proton
  | .finalAntiproton => .antiproton

/-- Panel in which a particle glyph occurs. -/
def FigureParticleGlyph.panel : FigureParticleGlyph → FigurePanel
  | .incidentProton => .initial
  | .targetProton => .initial
  | .finalProtonTop => .thresholdFinal
  | .finalProtonBottomLeft => .thresholdFinal
  | .finalProtonBottomRight => .thresholdFinal
  | .finalAntiproton => .thresholdFinal

/-!
Raster-level information from the image.  The positions are dimensionless
diagram coordinates, not physical spacetime positions.  They are kept apart
from the momenta and energies of the collision setup.
-/
structure AntiprotonProductionFigure where
  axisShown : FigurePanel → FigureAxis → Bool
  axisPrintedLabel : FigurePanel → FigureAxis → String
  glyphShown : FigureParticleGlyph → Bool
  glyphPosition : FigureParticleGlyph → ℝ × ℝ
  glyphPrintedLabel : FigureParticleGlyph → String
  glyphColor : FigureParticleGlyph → FigureColor
  initialVelocityArrowShown : Bool
  initialVelocityArrowDirection : HorizontalDirection
  initialVelocityArrowLabel : String
  finalCommonVelocityArrowShown : Bool
  finalCommonVelocityArrowDirection : HorizontalDirection
  panelsSeparatedByVerticalRule : Bool

/-! ## Physical collision setup -/

/-!
The independent physical quantities.  `fourMomentumGeV` stores laboratory
frame natural-unit readouts, while both rest energies and the unknown incident
threshold kinetic energy remain dimensionful physical quantities.

The common final four-velocity is an independent kinematic quantity.  The
governing-law premise below, rather than this record, relates it to outgoing
momenta and imposes its normalization.
-/
structure FixedTargetAntiprotonSetup where
  protonRestEnergy : DimEnergy
  antiprotonRestEnergy : DimEnergy
  incidentThresholdKineticEnergy : DimEnergy
  fourMomentumGeV : ReactionParticle → Lorentz.Vector 3
  commonFinalFourVelocity : Lorentz.Vector 3
  figure : AntiprotonProductionFigure

/-- Rest energy of an individually tracked particle. -/
def particleRestEnergy
    (setup : FixedTargetAntiprotonSetup)
    (particle : ReactionParticle) : DimEnergy :=
  match particle.species with
  | .proton => setup.protonRestEnergy
  | .antiproton => setup.antiprotonRestEnergy

/-- GeV readout of the requested threshold kinetic energy. -/
def incidentThresholdKineticEnergyGeV
    (setup : FixedTargetAntiprotonSetup) : ℝ :=
  energyInGigaElectronVolts setup.incidentThresholdKineticEnergy

/-! ## Scenario, figure evidence, and source data -/

/-!
Laboratory-frame facts stated by the prose and shown by the velocity arrows.
The target is at rest, the beam travels along positive `x`, and the threshold
cluster moves together along positive `x`.  No magnitude of the unknown beam
energy or speed is fixed here.
-/
structure MatchesFixedTargetThresholdScenario
    (setup : FixedTargetAntiprotonSetup) : Prop where
  targetHasZeroSpatialMomentum :
    Lorentz.Vector.spatialPart
        (setup.fourMomentumGeV .targetProton) = 0
  targetEnergyIsRestEnergy :
    Lorentz.Vector.timeComponent
        (setup.fourMomentumGeV .targetProton) =
      energyInGigaElectronVolts setup.protonRestEnergy
  incidentBeamMovesRight :
    0 < setup.fourMomentumGeV .incidentProton (Sum.inr 0)
  incidentBeamHasNoTransverseMomentum :
    setup.fourMomentumGeV .incidentProton (Sum.inr 1) = 0 ∧
      setup.fourMomentumGeV .incidentProton (Sum.inr 2) = 0
  finalClusterMovesRight :
    0 < setup.commonFinalFourVelocity (Sum.inr 0)
  finalClusterHasNoTransverseVelocity :
    setup.commonFinalFourVelocity (Sum.inr 1) = 0 ∧
      setup.commonFinalFourVelocity (Sum.inr 2) = 0

/-!
Primary-image evidence.  It records the axes, two initial proton glyphs, the
three-proton/one-antiproton final cluster, the `v` label, rightward arrows,
and the observed relative positions and colors.  None of these fields stores
the requested threshold kinetic energy.
-/
structure MatchesSuppliedAntiprotonFigure
    (setup : FixedTargetAntiprotonSetup) : Prop where
  everyAxisShown :
    ∀ panel axis, setup.figure.axisShown panel axis = true
  horizontalAxesLabeledX :
    ∀ panel, setup.figure.axisPrintedLabel panel .xAxis = "x"
  verticalAxesLabeledY :
    ∀ panel, setup.figure.axisPrintedLabel panel .yAxis = "y"
  everyParticleGlyphShown :
    ∀ glyph, setup.figure.glyphShown glyph = true
  everyProtonGlyphLabeledP :
    ∀ glyph,
      glyph.species = .proton →
        setup.figure.glyphPrintedLabel glyph = "p"
  antiprotonGlyphLabeled :
    setup.figure.glyphPrintedLabel .finalAntiproton = "p_bar"
  everyProtonGlyphLightBlue :
    ∀ glyph,
      glyph.species = .proton →
        setup.figure.glyphColor glyph = .lightBlue
  antiprotonGlyphGray :
    setup.figure.glyphColor .finalAntiproton = .gray
  targetAtDiagramOrigin :
    setup.figure.glyphPosition .targetProton = (0, 0)
  incidentProtonLeftOfTarget :
    (setup.figure.glyphPosition .incidentProton).1 <
      (setup.figure.glyphPosition .targetProton).1
  initialParticlesOnXAxis :
    (setup.figure.glyphPosition .incidentProton).2 = 0 ∧
      (setup.figure.glyphPosition .targetProton).2 = 0
  finalTopGlyphsAboveXAxis :
    0 < (setup.figure.glyphPosition .finalProtonTop).2 ∧
      0 < (setup.figure.glyphPosition .finalAntiproton).2
  finalBottomGlyphsBelowXAxis :
    (setup.figure.glyphPosition .finalProtonBottomLeft).2 < 0 ∧
      (setup.figure.glyphPosition .finalProtonBottomRight).2 < 0
  finalGlyphsRightOfYAxis :
    0 < (setup.figure.glyphPosition .finalProtonTop).1 ∧
      0 < (setup.figure.glyphPosition .finalProtonBottomLeft).1 ∧
      0 < (setup.figure.glyphPosition .finalProtonBottomRight).1 ∧
      0 < (setup.figure.glyphPosition .finalAntiproton).1
  initialArrowShown : setup.figure.initialVelocityArrowShown = true
  initialArrowPointsRight :
    setup.figure.initialVelocityArrowDirection = .rightward
  initialArrowLabel : setup.figure.initialVelocityArrowLabel = "v"
  finalArrowShown : setup.figure.finalCommonVelocityArrowShown = true
  finalArrowPointsRight :
    setup.figure.finalCommonVelocityArrowDirection = .rightward
  panelSeparatorShown :
    setup.figure.panelsSeparatedByVerticalRule = true

/-!
The numerical rest-energy datum and particle/antiparticle equality from the
problem prose.  `938 MeV` is a rest energy, not the unknown kinetic energy.
-/
structure MatchesProblemRestEnergyData
    (setup : FixedTargetAntiprotonSetup) : Prop where
  protonRestEnergyMeV :
    energyInMegaElectronVolts setup.protonRestEnergy = 938
  antiprotonHasSameRestEnergy :
    setup.antiprotonRestEnergy = setup.protonRestEnergy

/-!
Positivity and future-directedness assumptions selecting the physical branch
of the relativistic model.  They do not determine a numerical kinetic energy.
-/
structure HasPhysicalAntiprotonProductionParameters
    (setup : FixedTargetAntiprotonSetup) : Prop where
  protonRestEnergyPositive :
    0 < energyInGigaElectronVolts setup.protonRestEnergy
  antiprotonRestEnergyPositive :
    0 < energyInGigaElectronVolts setup.antiprotonRestEnergy
  incidentThresholdKineticEnergyNonnegative :
    0 ≤ incidentThresholdKineticEnergyGeV setup
  everyFourMomentumFutureDirected :
    ∀ particle,
      0 < Lorentz.Vector.timeComponent
        (setup.fourMomentumGeV particle)
  commonFinalFourVelocityFutureDirected :
    0 < Lorentz.Vector.timeComponent setup.commonFinalFourVelocity

/-! ## Governing relativistic laws -/

/-!
Mass-shell normalization, four-momentum conservation, the shared final
four-velocity threshold condition, and the general relation
`E_beam = K_beam + m_p c^2` in natural-unit readouts.

These are governing relations.  In particular, no field gives either
`K_beam = 6 m_p c^2` or the numerical answer `5.628 GeV`; both remain
consequences of the threshold kinematics.
-/
structure SatisfiesRelativisticThresholdLaws
    (setup : FixedTargetAntiprotonSetup) : Prop where
  particleMassShell :
    ∀ particle,
      Lorentz.Vector.minkowskiProduct
          (setup.fourMomentumGeV particle)
          (setup.fourMomentumGeV particle) =
        energyInGigaElectronVolts
            (particleRestEnergy setup particle) ^ 2
  commonFinalFourVelocityMassShell :
    Lorentz.Vector.minkowskiProduct
        setup.commonFinalFourVelocity
        setup.commonFinalFourVelocity = 1
  outgoingParticlesShareFourVelocity :
    ∀ particle,
      particle.IsOutgoing →
        setup.fourMomentumGeV particle =
          energyInGigaElectronVolts
              (particleRestEnergy setup particle) •
            setup.commonFinalFourVelocity
  fourMomentumConserved :
    setup.fourMomentumGeV .incidentProton +
        setup.fourMomentumGeV .targetProton =
      setup.fourMomentumGeV .outgoingProton₁ +
        setup.fourMomentumGeV .outgoingProton₂ +
        setup.fourMomentumGeV .outgoingProton₃ +
        setup.fourMomentumGeV .outgoingAntiproton
  incidentTotalEnergyDecomposition :
    Lorentz.Vector.timeComponent
        (setup.fourMomentumGeV .incidentProton) =
      incidentThresholdKineticEnergyGeV setup +
        energyInGigaElectronVolts setup.protonRestEnergy

/-! ## Answer choices and current target -/

/-- Labels of the four threshold-energy choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed threshold kinetic energy of each answer choice, in GeV. -/
def displayedThresholdEnergyGeV : AnswerChoice → ℝ
  | .A => 3901 / 1000
  | .B => 7581 / 1000
  | .C => 4364 / 1000
  | .D => 5628 / 1000

/-- A choice is correct when it equals the physical threshold-energy readout. -/
def MatchesDisplayedThresholdChoice
    (setup : FixedTargetAntiprotonSetup)
    (choice : AnswerChoice) : Prop :=
  incidentThresholdKineticEnergyGeV setup =
    displayedThresholdEnergyGeV choice

/-!
For a fixed proton target, conservation of the invariant mass gives

`(p_beam + p_target)^2 = (4 m_p)^2`.

Together with `p_target = (m_p, 0)`, this yields total beam energy `7 m_p`
and hence threshold kinetic energy `6 m_p`.  This intermediate relation is a
conclusion of the governing laws, not an input field.
-/
lemma incidentThresholdKineticEnergyGeV_eq_six_mul_restEnergy
    (setup : FixedTargetAntiprotonSetup)
    (hScenario : MatchesFixedTargetThresholdScenario setup)
    (hData : MatchesProblemRestEnergyData setup)
    (hPhysical : HasPhysicalAntiprotonProductionParameters setup)
    (hLaws : SatisfiesRelativisticThresholdLaws setup) :
    incidentThresholdKineticEnergyGeV setup =
      6 * energyInGigaElectronVolts setup.protonRestEnergy := by
  let m : ℝ := energyInGigaElectronVolts setup.protonRestEnergy
  let p := setup.fourMomentumGeV .incidentProton
  let t := setup.fourMomentumGeV .targetProton
  let u := setup.commonFinalFourVelocity
  have hp1 : setup.fourMomentumGeV .outgoingProton₁ = m • u := by
    simpa [m, u, particleRestEnergy, ReactionParticle.species] using
      hLaws.outgoingParticlesShareFourVelocity .outgoingProton₁ .proton₁
  have hp2 : setup.fourMomentumGeV .outgoingProton₂ = m • u := by
    simpa [m, u, particleRestEnergy, ReactionParticle.species] using
      hLaws.outgoingParticlesShareFourVelocity .outgoingProton₂ .proton₂
  have hp3 : setup.fourMomentumGeV .outgoingProton₃ = m • u := by
    simpa [m, u, particleRestEnergy, ReactionParticle.species] using
      hLaws.outgoingParticlesShareFourVelocity .outgoingProton₃ .proton₃
  have hpa : setup.fourMomentumGeV .outgoingAntiproton = m • u := by
    simpa [m, u, particleRestEnergy, ReactionParticle.species,
      hData.antiprotonHasSameRestEnergy] using
      hLaws.outgoingParticlesShareFourVelocity .outgoingAntiproton .antiproton
  have hcons : p + t = (4 * m) • u := by
    rw [hLaws.fourMomentumConserved, hp1, hp2, hp3, hpa]
    module
  have hpt : Lorentz.Vector.minkowskiProduct p t =
      Lorentz.Vector.timeComponent p * m := by
    rw [Lorentz.Vector.minkowskiProduct_eq_timeComponent_spatialPart]
    simp [t, m, hScenario.targetHasZeroSpatialMomentum,
      hScenario.targetEnergyIsRestEnergy]
  have htp : Lorentz.Vector.minkowskiProduct t p =
      m * Lorentz.Vector.timeComponent p := by
    rw [Lorentz.Vector.minkowskiProduct_symm]
    rw [hpt]
    ring
  have hpMass : Lorentz.Vector.minkowskiProduct p p = m ^ 2 := by
    simpa [p, m, particleRestEnergy, ReactionParticle.species] using
      hLaws.particleMassShell .incidentProton
  have htMass : Lorentz.Vector.minkowskiProduct t t = m ^ 2 := by
    simpa [t, m, particleRestEnergy, ReactionParticle.species] using
      hLaws.particleMassShell .targetProton
  have hInv := congrArg
    (fun v => Lorentz.Vector.minkowskiProduct v v) hcons
  simp only [map_add, map_smul, add_apply, smul_apply] at hInv
  rw [hpMass, htMass, hpt, htp,
    hLaws.commonFinalFourVelocityMassShell] at hInv
  norm_num [smul_eq_mul] at hInv
  have hm : 0 < m := by
    simpa [m] using hPhysical.protonRestEnergyPositive
  have hE : Lorentz.Vector.timeComponent p = 7 * m := by
    nlinarith
  rw [hLaws.incidentTotalEnergyDecomposition] at hE
  dsimp [m] at hE ⊢
  nlinarith

/-!
Since `m_p c^2 = 938 MeV = 0.938 GeV`, the threshold kinetic energy is

`6 * 0.938 GeV = 5.628 GeV`.

Thus the unique matching displayed answer is D.  The exact energy relation,
choice match, and uniqueness are all conclusions.

This formalizes `thm:physics:phyx_mini_0555:target`.
-/
theorem problem_phyx_mini_0555
    (setup : FixedTargetAntiprotonSetup)
    (hScenario : MatchesFixedTargetThresholdScenario setup)
    (hFigure : MatchesSuppliedAntiprotonFigure setup)
    (hData : MatchesProblemRestEnergyData setup)
    (hPhysical : HasPhysicalAntiprotonProductionParameters setup)
    (hLaws : SatisfiesRelativisticThresholdLaws setup) :
    incidentThresholdKineticEnergyGeV setup = 5628 / 1000 ∧
      MatchesDisplayedThresholdChoice setup .D ∧
      ∀ choice,
        MatchesDisplayedThresholdChoice setup choice → choice = .D := by
  have hRestMeV := hData.protonRestEnergyMeV
  have hRestGeV :
      energyInGigaElectronVolts setup.protonRestEnergy = 938 / 1000 := by
    dsimp [energyInMegaElectronVolts] at hRestMeV
    dsimp [energyInGigaElectronVolts]
    norm_num at hRestMeV ⊢
    linarith
  have hThreshold :
      incidentThresholdKineticEnergyGeV setup = 5628 / 1000 := by
    calc
      _ = 6 * energyInGigaElectronVolts setup.protonRestEnergy :=
        incidentThresholdKineticEnergyGeV_eq_six_mul_restEnergy
          setup hScenario hData hPhysical hLaws
      _ = _ := by rw [hRestGeV]; norm_num
  constructor
  · exact hThreshold
  constructor
  · simpa [MatchesDisplayedThresholdChoice, displayedThresholdEnergyGeV] using hThreshold
  · intro choice hChoice
    rcases choice with (_ | _ | _ | _) <;>
      simp_all [MatchesDisplayedThresholdChoice, displayedThresholdEnergyGeV]

end PhyXMiniProblems.ProblemPhyXMini0555
