import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0538

open Dimension

/-!
# Moment of inertia of a planar benzene molecule

The molecule is idealized as twelve point masses. Six carbon atoms form a
regular hexagon centered at `O`; six hydrogens form a concentric regular
hexagon and are attached radially to the carbons. The requested axis passes
through `O` perpendicular to the molecular plane.

Masses, lengths, and moments of inertia are unit-independent Physlib
quantities. Real numbers are used only for named-unit readouts, planar
coordinates explicitly measured in meters, angles explicitly measured in
degrees or radians, and the displayed answer values. In particular, the
requested moment of inertia is an independent observable constrained by the
point-mass law below; it is not defined to be the recorded answer.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- The physical dimension of a moment of inertia, mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical moment of inertia about a specified axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Read a physical mass in a selected Physlib mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Kilogram readout of an atom's mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Meter readout of a molecular length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometer readout of a molecular length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- SI readout of a moment of inertia, in kilogram-meter squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-! ## Molecular sites, geometry, and primary-figure vocabulary -/

/-- The two chemical species shown in the benzene diagram. -/
inductive AtomKind where
  | carbon
  | hydrogen
  deriving DecidableEq, Fintype, Repr

/-- One of the six angular positions occupied by each species. -/
structure AtomSite where
  kind : AtomKind
  vertex : Fin 6
  deriving DecidableEq, Fintype, Repr

/-- The carbon atom at angular position `i`. -/
def carbonSite (i : Fin 6) : AtomSite := ⟨.carbon, i⟩

/-- The hydrogen atom attached to the carbon at angular position `i`. -/
def hydrogenSite (i : Fin 6) : AtomSite := ⟨.hydrogen, i⟩

/-- The point-particle idealization used for every atom. -/
inductive AtomBodyModel where
  | pointMass
  deriving DecidableEq, Repr

/-- The qualitative shape of each species' six-atom ring. -/
inductive RingShape where
  | regularHexagon
  deriving DecidableEq, Repr

/-- Geometry of the axis requested in the question. -/
inductive RotationAxisGeometry where
  | throughCenterOPerpendicularToMolecularPlane
  deriving DecidableEq, Repr

/-- The two kinds of labeled bonds in the primary image. -/
inductive BondKind where
  | adjacentCarbonCarbon
  | attachedCarbonHydrogen
  deriving DecidableEq, Fintype, Repr

/-- Colors used by the atom legend in the primary image. -/
inductive FigureColor where
  | blue
  | orange
  deriving DecidableEq, Repr

/-- A scalar coordinate pair whose two components are explicitly in meters. -/
abbrev PlanarCoordinateMeters : Type := ℝ × ℝ

/-- Vertex `i` of a regular planar hexagon with a common angular phase. -/
def regularHexagonVertexMeters
    (center : PlanarCoordinateMeters) (radiusMeters phaseRadians : ℝ)
    (i : Fin 6) : PlanarCoordinateMeters :=
  let angle := phaseRadians + 2 * Real.pi * (i : ℝ) / 6
  (center.1 + radiusMeters * Real.cos angle,
    center.2 + radiusMeters * Real.sin angle)

/-- Euclidean distance between two explicitly meter-valued planar coordinates. -/
def planarDistanceMeters
    (p q : PlanarCoordinateMeters) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-!
Presentation-level data visible in the supplied image. Quantitative physical
lengths remain fields of the molecule setup; the figure stores only its
printed scalar readouts and labels.
-/
structure BenzeneFigure where
  atomShown : AtomSite → Bool
  atomColor : AtomKind → FigureColor
  atomLegendText : AtomKind → String
  bondShown : BondKind → Fin 6 → Bool
  distanceLabelNanometers : BondKind → ℝ
  interiorBondAngleDegrees : ℝ
  centerOShown : Bool
  centerLabel : String

/-!
The physical molecule and its observables. The planar coordinates explicitly
encode coplanarity. Neither the axis distances nor the moment of inertia are
defined from the requested answer; their geometric and dynamical relations
are imposed separately below.
-/
structure BenzeneMoleculeSetup where
  atomBodyModel : AtomBodyModel
  ringShape : AtomKind → RingShape
  askedAxisGeometry : RotationAxisGeometry
  centerOPositionMeters : PlanarCoordinateMeters
  atomPositionInPlaneMeters : AtomSite → PlanarCoordinateMeters
  atomMass : AtomKind → MassQuantity
  adjacentCarbonCarbonSeparation : LengthQuantity
  attachedCarbonHydrogenSeparation : LengthQuantity
  distanceFromAskedAxis : AtomSite → LengthQuantity
  momentOfInertiaAboutAskedAxis : MomentOfInertiaQuantity
  figure : BenzeneFigure

/-! ## Scenario, readouts, geometry, and governing law -/

/-- Qualitative molecular and rotation-axis model stated in the problem. -/
structure MatchesBenzeneScenario (setup : BenzeneMoleculeSetup) : Prop where
  atomsArePointMasses : setup.atomBodyModel = .pointMass
  carbonRingIsRegularHexagon : setup.ringShape .carbon = .regularHexagon
  hydrogenRingIsRegularHexagon : setup.ringShape .hydrogen = .regularHexagon
  requestedAxis : setup.askedAxisGeometry =
    .throughCenterOPerpendicularToMolecularPlane

/-!
Numerical data stated in the problem: carbon and hydrogen atom masses and the
two center-to-center separations. No moment-of-inertia value occurs here.
-/
structure MatchesProblemReadouts (setup : BenzeneMoleculeSetup) : Prop where
  carbonAtomMassKilograms :
    massInKilograms (setup.atomMass .carbon) = (199 / 10 ^ 28 : ℝ)
  hydrogenAtomMassKilograms :
    massInKilograms (setup.atomMass .hydrogen) = (167 / 10 ^ 29 : ℝ)
  adjacentCarbonCarbonNanometers :
    lengthInNanometers setup.adjacentCarbonCarbonSeparation = (11 / 100 : ℝ)
  attachedCarbonHydrogenNanometers :
    lengthInNanometers setup.attachedCarbonHydrogenSeparation = (1 / 10 : ℝ)

/-!
Literal readouts from the primary image: six atoms of each species, six bonds
of each kind, the blue `H` and orange `C` legend, center label `O`, distance
labels `0.110 nm` and `0.100 nm`, and the `120 degree` bond-angle label.
-/
structure MatchesPrimaryFigure (setup : BenzeneMoleculeSetup) : Prop where
  everyAtomShown : ∀ site : AtomSite, setup.figure.atomShown site = true
  everyBondShown : ∀ (kind : BondKind) (i : Fin 6),
    setup.figure.bondShown kind i = true
  hydrogenColor : setup.figure.atomColor .hydrogen = .blue
  carbonColor : setup.figure.atomColor .carbon = .orange
  hydrogenLegend : setup.figure.atomLegendText .hydrogen = "H"
  carbonLegend : setup.figure.atomLegendText .carbon = "C"
  centerShown : setup.figure.centerOShown = true
  centerText : setup.figure.centerLabel = "O"
  carbonCarbonDistanceLabel :
    setup.figure.distanceLabelNanometers .adjacentCarbonCarbon = 11 / 100
  carbonHydrogenDistanceLabel :
    setup.figure.distanceLabelNanometers .attachedCarbonHydrogen = 1 / 10
  carbonCarbonLabelMatchesLength :
    setup.figure.distanceLabelNanometers .adjacentCarbonCarbon =
      lengthInNanometers setup.adjacentCarbonCarbonSeparation
  carbonHydrogenLabelMatchesLength :
    setup.figure.distanceLabelNanometers .attachedCarbonHydrogen =
      lengthInNanometers setup.attachedCarbonHydrogenSeparation
  interiorBondAngle : setup.figure.interiorBondAngleDegrees = 120

/-!
The two species occupy concentric regular hexagons with a common angular
phase. For a regular hexagon the carbon ring's radius equals its side length;
each attached hydrogen lies radially outward by one C-H separation. The last
two fields state the corresponding perpendicular distances to the normal axis
in every coherent length unit. These are geometric inputs, not inertia data.
-/
structure MatchesPlanarRegularHexagonGeometry
    (setup : BenzeneMoleculeSetup) : Prop where
  commonAngularPhase : ∃ phaseRadians : ℝ,
    (∀ i : Fin 6,
      setup.atomPositionInPlaneMeters (carbonSite i) =
        regularHexagonVertexMeters setup.centerOPositionMeters
          (lengthInMeters setup.adjacentCarbonCarbonSeparation)
          phaseRadians i) ∧
    (∀ i : Fin 6,
      setup.atomPositionInPlaneMeters (hydrogenSite i) =
        regularHexagonVertexMeters setup.centerOPositionMeters
          (lengthInMeters setup.adjacentCarbonCarbonSeparation +
            lengthInMeters setup.attachedCarbonHydrogenSeparation)
          phaseRadians i)
  adjacentCarbonDistances : ∀ i : Fin 6,
    planarDistanceMeters
        (setup.atomPositionInPlaneMeters (carbonSite i))
        (setup.atomPositionInPlaneMeters (carbonSite (i + 1))) =
      lengthInMeters setup.adjacentCarbonCarbonSeparation
  attachedCarbonHydrogenDistances : ∀ i : Fin 6,
    planarDistanceMeters
        (setup.atomPositionInPlaneMeters (carbonSite i))
        (setup.atomPositionInPlaneMeters (hydrogenSite i)) =
      lengthInMeters setup.attachedCarbonHydrogenSeparation
  carbonAxisRadius : ∀ (i : Fin 6) (unit : LengthUnit),
    lengthReadout unit (setup.distanceFromAskedAxis (carbonSite i)) =
      lengthReadout unit setup.adjacentCarbonCarbonSeparation
  hydrogenAxisRadius : ∀ (i : Fin 6) (unit : LengthUnit),
    lengthReadout unit (setup.distanceFromAskedAxis (hydrogenSite i)) =
      lengthReadout unit setup.adjacentCarbonCarbonSeparation +
        lengthReadout unit setup.attachedCarbonHydrogenSeparation

/-- Positivity and nondegeneracy conditions for the physical molecule. -/
structure HasPhysicalBenzeneParameters (setup : BenzeneMoleculeSetup) : Prop where
  carbonMassPositive : 0 < massInKilograms (setup.atomMass .carbon)
  hydrogenMassPositive : 0 < massInKilograms (setup.atomMass .hydrogen)
  carbonCarbonSeparationPositive :
    0 < lengthInMeters setup.adjacentCarbonCarbonSeparation
  carbonHydrogenSeparationPositive :
    0 < lengthInMeters setup.attachedCarbonHydrogenSeparation
  everyAxisDistancePositive : ∀ site : AtomSite,
    0 < lengthInMeters (setup.distanceFromAskedAxis site)
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutAskedAxis

/-!
The general point-mass law `I = sum m_i r_i^2`, stated in every coherent mass
and length unit. It contains neither the benzene-specific simplified formula
nor any displayed numerical answer.
-/
structure SatisfiesPointMassMomentOfInertiaLaw
    (setup : BenzeneMoleculeSetup) : Prop where
  inertiaIsPointMassSum : ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
    momentOfInertiaReadout massUnit lengthUnit
        setup.momentOfInertiaAboutAskedAxis =
      ∑ site : AtomSite,
        massReadout massUnit (setup.atomMass site.kind) *
          lengthReadout lengthUnit (setup.distanceFromAskedAxis site) ^ 2

/-! ## Displayed choices and derived conclusions -/

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed moments of inertia, read in kilogram-meter squared. -/
def displayedMomentOfInertia : AnswerChoice → ℝ
  | .A => 231 / 10 ^ 47
  | .B => 165 / 10 ^ 47
  | .C => 105 / 10 ^ 47
  | .D => 189 / 10 ^ 47

/-- One unit in the final displayed digit of every answer choice. -/
def displayedResolution : ℝ := 1 / 10 ^ 47

/-- Rounding agreement with a displayed answer choice. -/
def MatchesAnswerChoice
    (setup : BenzeneMoleculeSetup) (choice : AnswerChoice) : Prop :=
  |momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAskedAxis -
      displayedMomentOfInertia choice| < displayedResolution / 2

/-- Every carbon lies one C-C side length from the normal axis through `O`. -/
lemma carbon_axis_radius_in_meters
    (setup : BenzeneMoleculeSetup)
    (hGeometry : MatchesPlanarRegularHexagonGeometry setup)
    (i : Fin 6) :
    lengthInMeters (setup.distanceFromAskedAxis (carbonSite i)) =
      lengthInMeters setup.adjacentCarbonCarbonSeparation := by
  exact hGeometry.carbonAxisRadius i LengthUnit.meters

/-- Every hydrogen radius is the carbon radius plus one radial C-H bond. -/
lemma hydrogen_axis_radius_in_meters
    (setup : BenzeneMoleculeSetup)
    (hGeometry : MatchesPlanarRegularHexagonGeometry setup)
    (i : Fin 6) :
    lengthInMeters (setup.distanceFromAskedAxis (hydrogenSite i)) =
      lengthInMeters setup.adjacentCarbonCarbonSeparation +
        lengthInMeters setup.attachedCarbonHydrogenSeparation := by
  exact hGeometry.hydrogenAxisRadius i LengthUnit.meters

/-!
Grouping the twelve terms of the general point-mass sum by species gives six
equal carbon contributions and six equal hydrogen contributions. This formula
is derived from geometry and the general law; it is not a premise.
-/
lemma benzene_point_mass_inertia_formula
    (setup : BenzeneMoleculeSetup)
    (hGeometry : MatchesPlanarRegularHexagonGeometry setup)
    (hInertia : SatisfiesPointMassMomentOfInertiaLaw setup) :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutAskedAxis =
      6 * massInKilograms (setup.atomMass .carbon) *
          lengthInMeters setup.adjacentCarbonCarbonSeparation ^ 2 +
        6 * massInKilograms (setup.atomMass .hydrogen) *
          (lengthInMeters setup.adjacentCarbonCarbonSeparation +
            lengthInMeters setup.attachedCarbonHydrogenSeparation) ^ 2 := by
  classical
  change
    momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters
        setup.momentOfInertiaAboutAskedAxis =
      _
  rw [hInertia.inertiaIsPointMassSum MassUnit.kilograms LengthUnit.meters]
  let e : AtomSite ≃ AtomKind × Fin 6 :=
    { toFun := fun site => (site.kind, site.vertex)
      invFun := fun pair => ⟨pair.1, pair.2⟩
      left_inv := by rintro ⟨kind, vertex⟩; rfl
      right_inv := by rintro ⟨kind, vertex⟩; rfl }
  rw [Fintype.sum_equiv e
    (fun site =>
      massReadout MassUnit.kilograms (setup.atomMass site.kind) *
        lengthReadout LengthUnit.meters
          (setup.distanceFromAskedAxis site) ^ 2)
    (fun pair =>
      massReadout MassUnit.kilograms (setup.atomMass pair.1) *
        lengthReadout LengthUnit.meters
          (setup.distanceFromAskedAxis ⟨pair.1, pair.2⟩) ^ 2)
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  have hKinds :
      (Finset.univ : Finset AtomKind) = {.carbon, .hydrogen} := by
    decide
  rw [hKinds]
  have hCarbon : ∀ i : Fin 6,
      lengthReadout LengthUnit.meters
          (setup.distanceFromAskedAxis ⟨.carbon, i⟩) =
        lengthReadout LengthUnit.meters
          setup.adjacentCarbonCarbonSeparation := by
    intro i
    exact hGeometry.carbonAxisRadius i LengthUnit.meters
  have hHydrogen : ∀ i : Fin 6,
      lengthReadout LengthUnit.meters
          (setup.distanceFromAskedAxis ⟨.hydrogen, i⟩) =
        lengthReadout LengthUnit.meters
            setup.adjacentCarbonCarbonSeparation +
          lengthReadout LengthUnit.meters
            setup.attachedCarbonHydrogenSeparation := by
    intro i
    exact hGeometry.hydrogenAxisRadius i LengthUnit.meters
  simp [hCarbon, hHydrogen, massInKilograms, lengthInMeters]
  ring

/-!
The supplied masses and geometry give the exact SI readout
`1886622 / 10^51 kg m^2 = 1.886622 * 10^-45 kg m^2`. It rounds to
`1.89 * 10^-45 kg m^2`, uniquely selecting choice D.

This is the formal target corresponding to
`thm:physics:phyx_mini_0538:target`.
-/
theorem benzene_molecule_moment_of_inertia
    (setup : BenzeneMoleculeSetup)
    (hScenario : MatchesBenzeneScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hGeometry : MatchesPlanarRegularHexagonGeometry setup)
    (hPhysical : HasPhysicalBenzeneParameters setup)
    (hInertia : SatisfiesPointMassMomentOfInertiaLaw setup) :
    momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAskedAxis =
        (1886622 / 10 ^ 51 : ℝ) ∧
      MatchesAnswerChoice setup .D ∧
      ∀ choice : AnswerChoice, choice ≠ .D →
        |momentOfInertiaInKilogramMetersSquared
              setup.momentOfInertiaAboutAskedAxis -
            displayedMomentOfInertia .D| <
          |momentOfInertiaInKilogramMetersSquared
              setup.momentOfInertiaAboutAskedAxis -
            displayedMomentOfInertia choice| := by
  have nanometers_eq_meters (length : LengthQuantity) :
      lengthInNanometers length =
        1000000000 * lengthInMeters length := by
    have hUnits := length.2 UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
    have hUnitsVal :=
      congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ)) hUnits
    change lengthInNanometers length = _ at hUnitsVal
    simp [UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
      LengthUnit.scale] at hUnitsVal
    norm_num [LengthUnit.div_eq_val, NNReal.coe_div] at hUnitsVal
    change lengthInNanometers length =
      1000000000 * lengthInMeters length at hUnitsVal
    exact hUnitsVal
  have hCarbonMeters :
      lengthInMeters setup.adjacentCarbonCarbonSeparation =
        (11 / 10 ^ 11 : ℝ) := by
    have h :=
      nanometers_eq_meters setup.adjacentCarbonCarbonSeparation
    rw [hReadouts.adjacentCarbonCarbonNanometers] at h
    norm_num at h ⊢
    linarith
  have hHydrogenMeters :
      lengthInMeters setup.attachedCarbonHydrogenSeparation =
        (1 / 10 ^ 10 : ℝ) := by
    have h :=
      nanometers_eq_meters setup.attachedCarbonHydrogenSeparation
    rw [hReadouts.attachedCarbonHydrogenNanometers] at h
    norm_num at h ⊢
    linarith
  have hExact :=
    benzene_point_mass_inertia_formula setup hGeometry hInertia
  rw [hReadouts.carbonAtomMassKilograms,
    hReadouts.hydrogenAtomMassKilograms, hCarbonMeters,
    hHydrogenMeters] at hExact
  norm_num at hExact
  have hExactTarget :
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutAskedAxis =
        (1886622 / 10 ^ 51 : ℝ) := by
    norm_num at hExact ⊢
    exact hExact
  refine ⟨hExactTarget, ?_, ?_⟩
  · rw [MatchesAnswerChoice, hExactTarget]
    norm_num [displayedMomentOfInertia, displayedResolution]
  · intro choice hNotD
    rw [hExactTarget]
    cases choice with
    | A => norm_num [displayedMomentOfInertia]
    | B => norm_num [displayedMomentOfInertia]
    | C => norm_num [displayedMomentOfInertia]
    | D => exact (hNotD rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0538
