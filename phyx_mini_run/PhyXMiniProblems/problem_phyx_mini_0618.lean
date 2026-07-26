import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Disintegration energy of uranium-232 alpha decay

A neutral uranium-232 atom decays to thorium-228 while emitting an alpha
particle.  Because the supplied parent and daughter masses are neutral-atom
masses, the mass defect is computed with the neutral helium-4 atomic mass:
the two electrons in neutral helium account for the two electrons absent from
the neutral thorium daughter relative to neutral uranium.

The supplied figure is a qualitative two-body recoil diagram.  It places the
alpha particle on the left with a leftward velocity arrow labelled
`vec V_alpha` and the daughter nucleus on the right with a rightward velocity
arrow labelled `vec V_D`; the corresponding mass labels are `m_alpha` and
`m_D`.  The raster gives neither a calibrated speed nor a calibrated mass.

Masses, velocities, and energies below are unit-independent Physlib
quantities.  Real numbers occur only as named-unit readouts, dimensionless
nuclear counts, qualitative figure coordinates, or displayed MeV values.

Assumption/target boundary:

* `MatchesAlphaDecayProblemData` contains the stated uranium/thorium channel
  and the two supplied neutral-atom masses.
* `MatchesReferenceAtomicData` contains the helium-4 neutral-atom mass needed
  to use neutral-atom mass bookkeeping.
* `MatchesPrimaryAlphaDecayFigure` contains the product labels, mass and
  velocity labels, colors, ordering, and opposite arrow directions visible in
  the primary raster.
* `SatisfiesAlphaDecayEnergyLaws` contains nucleon/charge conservation, the
  general neutral-atom mass-defect relation, and `Q = Delta m c^2`.
* There are no previous-part results.
* The requested rounded value `5.4 MeV` and answer C occur only in the
  displayed-answer table and theorem conclusion, never in a premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0618

open Dimension

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical rest mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/--
A unit-independent velocity vector in the two-dimensional plane of the
supplied recoil diagram.
-/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) (Fin 2 → ℝ))

/-- The two coordinate directions in the recoil diagram. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Coordinate index associated with a diagram axis. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .horizontal => 0
  | .vertical => 1

/-- Kilogram readout of a physical mass in coherent SI units. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- The SI kilogram value used for one unified atomic mass unit. -/
def atomicMassUnitInKilograms : ℝ :=
  1.66053906660e-27

/-- Unified-atomic-mass-unit readout of a physical mass. -/
def massInAtomicMassUnits (mass : MassQuantity) : ℝ :=
  massInKilograms mass / atomicMassUnitInKilograms

/-- One component of a planar velocity, read in metres per second. -/
def velocityComponentInMetersPerSecond
    (velocity : PlanarVelocityQuantity) (axis : DiagramAxis) : ℝ :=
  (velocity UnitChoices.SI).val axis.toFin

/-- Joule readout of a dimensionful energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Physlib's exact electron volt, read in joules. -/
def electronVoltInJoules : ℝ :=
  (DimEnergy.electronVolt UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- A physical energy expressed as a numerical number of megaelectronvolts. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy /
    ((1_000_000 : ℝ) * electronVoltInJoules)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Nuclides and the alpha-decay channel -/

/-- The three nuclides used in the decay and neutral-atom mass balance. -/
inductive Nuclide where
  | uranium232
  | thorium228
  | helium4
  deriving DecidableEq, Fintype, Repr

/-- Proton number `Z` of each nuclide. -/
def Nuclide.atomicNumber : Nuclide → ℕ
  | .uranium232 => 92
  | .thorium228 => 90
  | .helium4 => 2

/-- Nucleon (mass) number `A` of each nuclide. -/
def Nuclide.massNumber : Nuclide → ℕ
  | .uranium232 => 232
  | .thorium228 => 228
  | .helium4 => 4

/--
The parent, daughter, and emitted nuclide identities in one nuclear decay
channel.  The emitted helium-4 nucleus is the physical alpha particle.
-/
structure AlphaDecayChannel where
  parent : Nuclide
  daughter : Nuclide
  emitted : Nuclide

/-- Conservation of nucleon number and proton number in a decay channel. -/
def ConservesNuclearNumbers (channel : AlphaDecayChannel) : Prop :=
  channel.parent.massNumber =
      channel.daughter.massNumber + channel.emitted.massNumber ∧
    channel.parent.atomicNumber =
      channel.daughter.atomicNumber + channel.emitted.atomicNumber

/-! ## Decay products and primary-figure vocabulary -/

/-- The two physical products represented by circles in the supplied image. -/
inductive DecayProduct where
  | alphaParticle
  | daughterNucleus
  deriving DecidableEq, Fintype, Repr

/-- Textual object labels visible above the two product markers. -/
inductive ProductFigureLabel where
  | alphaParticle
  | daughterNucleus
  deriving DecidableEq, Repr

/-- Symbolic mass labels printed below the two products. -/
inductive MassFigureLabel where
  | mAlpha
  | mDaughter
  deriving DecidableEq, Repr

/-- Symbolic velocity-vector labels printed beside the arrows. -/
inductive VelocityFigureLabel where
  | vAlpha
  | vDaughter
  deriving DecidableEq, Repr

/-- Qualitative horizontal arrow directions in the supplied image. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Marker colors used in the raster. -/
inductive MarkerColor where
  | pink
  deriving DecidableEq, Repr

/-- Velocity-arrow colors used in the raster. -/
inductive ArrowColor where
  | green
  deriving DecidableEq, Repr

/--
Presentation-level evidence transcribed from image 618.  Its horizontal
coordinates preserve only left-to-right ordering and are not physical
distances.
-/
structure AlphaDecayFigure where
  productShown : DecayProduct → Bool
  productHorizontalCoordinate : DecayProduct → ℝ
  productLabel : DecayProduct → ProductFigureLabel
  productMarkerColor : DecayProduct → MarkerColor
  massLabel : DecayProduct → MassFigureLabel
  velocityArrowShown : DecayProduct → Bool
  velocityArrowDirection : DecayProduct → HorizontalDirection
  velocityArrowColor : DecayProduct → ArrowColor
  velocityLabel : DecayProduct → VelocityFigureLabel
  hasQuantitativeMassOrSpeedScale : Bool

/-! ## Independent physical setup -/

/--
All independent physical quantities in the decay setup.

The neutral-atom masses used for Q-value bookkeeping are kept distinct from
the actual bare alpha-particle and daughter-nucleus masses labelled in the
figure.  The mass defect and disintegration energy are independent fields;
neither is defined from a displayed answer.
-/
structure Uranium232AlphaDecaySetup where
  channel : AlphaDecayChannel
  neutralAtomRestMass : Nuclide → MassQuantity
  alphaParticleRestMass : MassQuantity
  daughterNucleusRestMass : MassQuantity
  productVelocity : DecayProduct → PlanarVelocityQuantity
  massDefect : MassQuantity
  disintegrationEnergy : DimEnergy
  figure : AlphaDecayFigure

/-- Physical rest mass associated with a product's `m_alpha` or `m_D` label. -/
def productRestMass
    (setup : Uranium232AlphaDecaySetup) : DecayProduct → MassQuantity
  | .alphaParticle => setup.alphaParticleRestMass
  | .daughterNucleus => setup.daughterNucleusRestMass

/-! ## Stated data, reference data, and primary-image evidence -/

/--
The decay identities and the two neutral-atom masses explicitly supplied in
the prose.  Decimal values are represented exactly by rational numbers.
-/
structure MatchesAlphaDecayProblemData
    (setup : Uranium232AlphaDecaySetup) : Prop where
  parentIsUranium232 : setup.channel.parent = .uranium232
  daughterIsThorium228 : setup.channel.daughter = .thorium228
  emittedNuclideIsHelium4 : setup.channel.emitted = .helium4
  uranium232NeutralAtomMass :
    massInAtomicMassUnits
        (setup.neutralAtomRestMass .uranium232) =
      (232_037_156 / 1_000_000 : ℝ)
  thorium228NeutralAtomMass :
    massInAtomicMassUnits
        (setup.neutralAtomRestMass .thorium228) =
      (228_028_741 / 1_000_000 : ℝ)

/--
Calibrated helium-4 neutral-atom mass required by the neutral-atom Q-value
calculation.  This is reference nuclear data, not the requested energy.
-/
structure MatchesReferenceAtomicData
    (setup : Uranium232AlphaDecaySetup) : Prop where
  helium4NeutralAtomMass :
    massInAtomicMassUnits
        (setup.neutralAtomRestMass .helium4) =
      (4_002_603 / 1_000_000 : ℝ)

/--
Labels, marker colors, ordering, and outward velocity arrows read from the
primary bitmap.  The component signs connect the drawn vector labels to the
dimensionful velocities without assigning their magnitudes.
-/
structure MatchesPrimaryAlphaDecayFigure
    (setup : Uranium232AlphaDecaySetup) : Prop where
  bothProductsShown :
    ∀ product, setup.figure.productShown product = true
  alphaIsDrawnLeftOfDaughter :
    setup.figure.productHorizontalCoordinate .alphaParticle <
      setup.figure.productHorizontalCoordinate .daughterNucleus
  alphaObjectLabel :
    setup.figure.productLabel .alphaParticle = .alphaParticle
  daughterObjectLabel :
    setup.figure.productLabel .daughterNucleus = .daughterNucleus
  bothMarkersPink :
    ∀ product, setup.figure.productMarkerColor product = .pink
  alphaMassLabel :
    setup.figure.massLabel .alphaParticle = .mAlpha
  daughterMassLabel :
    setup.figure.massLabel .daughterNucleus = .mDaughter
  bothVelocityArrowsShown :
    ∀ product, setup.figure.velocityArrowShown product = true
  alphaArrowPointsLeft :
    setup.figure.velocityArrowDirection .alphaParticle = .left
  daughterArrowPointsRight :
    setup.figure.velocityArrowDirection .daughterNucleus = .right
  bothVelocityArrowsGreen :
    ∀ product, setup.figure.velocityArrowColor product = .green
  alphaVelocityLabel :
    setup.figure.velocityLabel .alphaParticle = .vAlpha
  daughterVelocityLabel :
    setup.figure.velocityLabel .daughterNucleus = .vDaughter
  alphaVelocityHasNegativeHorizontalComponent :
    velocityComponentInMetersPerSecond
        (setup.productVelocity .alphaParticle) .horizontal < 0
  daughterVelocityHasPositiveHorizontalComponent :
    0 < velocityComponentInMetersPerSecond
        (setup.productVelocity .daughterNucleus) .horizontal
  bothVelocitiesAreHorizontal :
    ∀ product,
      velocityComponentInMetersPerSecond
          (setup.productVelocity product) .vertical = 0
  noQuantitativeMassOrSpeedScale :
    setup.figure.hasQuantitativeMassOrSpeedScale = false

/-! ## Physical domain and governing laws -/

/-- Positivity and nondegeneracy conditions for the physical decay branch. -/
structure HasPhysicalAlphaDecayParameters
    (setup : Uranium232AlphaDecaySetup) : Prop where
  everyNeutralAtomMassPositive :
    ∀ nuclide, 0 < massInKilograms (setup.neutralAtomRestMass nuclide)
  everyProductRestMassPositive :
    ∀ product, 0 < massInKilograms (productRestMass setup product)
  massDefectPositive : 0 < massInKilograms setup.massDefect
  disintegrationEnergyPositive :
    0 < energyInJoules setup.disintegrationEnergy
  atomicMassUnitPositive : 0 < atomicMassUnitInKilograms
  electronVoltPositive : 0 < electronVoltInJoules
  speedOfLightPositive : 0 < speedOfLightInMetersPerSecond

/-!
Governing relations for alpha-decay energy:

* the channel conserves nucleon number and proton number;
* because the neutral electron counts balance, the mass defect is the parent
  neutral-atom mass minus the daughter and neutral-helium masses; and
* the released disintegration energy obeys `Q = Delta m c^2`.

No field mentions `5.4 MeV` or any answer choice.
-/
structure SatisfiesAlphaDecayEnergyLaws
    (setup : Uranium232AlphaDecaySetup) : Prop where
  nuclearNumberConservation :
    ConservesNuclearNumbers setup.channel
  neutralAtomMassDefect :
    massInKilograms setup.massDefect =
      massInKilograms
          (setup.neutralAtomRestMass setup.channel.parent) -
        massInKilograms
          (setup.neutralAtomRestMass setup.channel.daughter) -
        massInKilograms
          (setup.neutralAtomRestMass setup.channel.emitted)
  massEnergyEquivalence :
    energyInJoules setup.disintegrationEnergy =
      massInKilograms setup.massDefect *
        speedOfLightInMetersPerSecond ^ 2

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate disintegration energies. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical MeV value printed beside each answer label. -/
def AnswerChoice.energyMegaElectronVolts : AnswerChoice → ℝ
  | .A => 5
  | .B => 26 / 5
  | .C => 27 / 5
  | .D => 24 / 5

/-- Dataset metadata records answer C; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice :=
  .C

/--
Agreement with an energy displayed to one decimal place: the calculated
value lies within half of the last displayed decimal unit.
-/
def MatchesDisplayedDisintegrationEnergy
    (energy : DimEnergy) (choice : AnswerChoice) : Prop :=
  |energyInMegaElectronVolts energy -
      choice.energyMegaElectronVolts| ≤ (1 / 20 : ℝ)

/-!
The supplied neutral-atom masses give the mass defect

`232.037156 u - 228.028741 u - 4.002603 u = 0.005812 u`.

Mass-energy equivalence then gives the exact SI-calibrated expression below,
whose value agrees at the displayed one-decimal precision with `5.4 MeV`,
answer C.

Blueprint label: `thm:physics:phyx_mini_0618:target`.
-/
theorem problem_phyx_mini_0618
    (setup : Uranium232AlphaDecaySetup)
    (_problem : MatchesAlphaDecayProblemData setup)
    (_reference : MatchesReferenceAtomicData setup)
    (_figure : MatchesPrimaryAlphaDecayFigure setup)
    (_physical : HasPhysicalAlphaDecayParameters setup)
    (_laws : SatisfiesAlphaDecayEnergyLaws setup) :
    massInAtomicMassUnits setup.massDefect =
        (5_812 / 1_000_000 : ℝ) ∧
      energyInMegaElectronVolts setup.disintegrationEnergy =
        ((((232_037_156 / 1_000_000 : ℝ) -
              (228_028_741 / 1_000_000 : ℝ) -
              (4_002_603 / 1_000_000 : ℝ)) *
            atomicMassUnitInKilograms) *
          speedOfLightInMetersPerSecond ^ 2) /
        ((1_000_000 : ℝ) * electronVoltInJoules) ∧
      MatchesDisplayedDisintegrationEnergy
        setup.disintegrationEnergy recordedAnswerChoice ∧
      recordedAnswerChoice = .C := by
  have hAmuNe : atomicMassUnitInKilograms ≠ 0 :=
    ne_of_gt _physical.atomicMassUnitPositive
  have mass_eq_mul_amu (mass : MassQuantity) (value : ℝ)
      (h : massInAtomicMassUnits mass = value) :
      massInKilograms mass = value * atomicMassUnitInKilograms := by
    rw [massInAtomicMassUnits] at h
    field_simp [hAmuNe] at h ⊢
    nlinarith
  have hUkg :=
    mass_eq_mul_amu _ _ _problem.uranium232NeutralAtomMass
  have hThkg :=
    mass_eq_mul_amu _ _ _problem.thorium228NeutralAtomMass
  have hHekg :=
    mass_eq_mul_amu _ _ _reference.helium4NeutralAtomMass
  have hDefectKg :
      massInKilograms setup.massDefect =
        (((232_037_156 / 1_000_000 : ℝ) -
            (228_028_741 / 1_000_000 : ℝ) -
            (4_002_603 / 1_000_000 : ℝ)) *
          atomicMassUnitInKilograms) := by
    rw [_laws.neutralAtomMassDefect,
      _problem.parentIsUranium232, _problem.daughterIsThorium228,
      _problem.emittedNuclideIsHelium4, hUkg, hThkg, hHekg]
    ring
  have hDefectU :
      massInAtomicMassUnits setup.massDefect =
        (5_812 / 1_000_000 : ℝ) := by
    rw [massInAtomicMassUnits, hDefectKg]
    field_simp [hAmuNe]
    norm_num
  have hEnergyMeV :
      energyInMegaElectronVolts setup.disintegrationEnergy =
        ((((232_037_156 / 1_000_000 : ℝ) -
              (228_028_741 / 1_000_000 : ℝ) -
              (4_002_603 / 1_000_000 : ℝ)) *
            atomicMassUnitInKilograms) *
          speedOfLightInMetersPerSecond ^ 2) /
        ((1_000_000 : ℝ) * electronVoltInJoules) := by
    rw [energyInMegaElectronVolts, _laws.massEnergyEquivalence, hDefectKg]
  have hC : speedOfLightInMetersPerSecond = 299792458 := by
    simp [speedOfLightInMetersPerSecond]
  have hEv :
      electronVoltInJoules = (1602176634 / 10 ^ 28 : ℝ) := by
    simp [electronVoltInJoules, DimEnergy.electronVolt, DimEnergy.joule,
      CarriesDimension.toDimensionful_apply_apply]
    norm_num
  refine ⟨hDefectU, hEnergyMeV, ?_, rfl⟩
  rw [MatchesDisplayedDisintegrationEnergy, hEnergyMeV, hC, hEv]
  norm_num [recordedAnswerChoice, AnswerChoice.energyMegaElectronVolts,
    atomicMassUnitInKilograms, abs_of_pos]

end PhyXMiniProblems.ProblemPhyXMini0618
