import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0625

open Dimension
open scoped BigOperators

/-!
# Latent heat of fusion of a weakly bound simple-cubic solid

The solid is monatomic and every bulk atom has six nearest neighbours. Bonds
are undirected, so the degree-sum formula counts each physical bond twice and
gives three bonds per atom. Melting is assumed to spend its latent heat on
breaking these bonds, each of binding energy `3.4 * 10⁻³ eV`.

The supplied raster has no text or numerical labels. It shows uniformly
spaced yellow spherical sites in three-dimensional cubic layers, joined by
black nearest-neighbour line segments. These qualitative presentation data
are kept separate from the finite bulk bond graph used for bond counting.

Physlib supplies dimensionful energy and its exact electron-volt unit. Its
MLT dimension system has no amount-of-substance dimension, so molar latent
heat is kept behind an abstract physical-quantity/readout interface. Real
numbers occur only at calibrated unit boundaries, for counts per mole, and
in displayed multiple-choice values.
-/

/-! ## Physical quantities and calibrated readouts -/

/--
An abstract carrier for molar energies, together with its scalar readout in
joules per mole. A molar energy is therefore not identified with `ℝ`.
-/
structure MolarEnergyScale where
  Quantity : Type
  inJoulesPerMole : Quantity → ℝ

/-- Read a dimensionful energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- The coherent-SI joule value of Physlib's exact electron volt. -/
def electronVoltInJoules : ℝ :=
  energyInJoules DimEnergy.electronVolt

/-- Read a physical energy in electron volts. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / electronVoltInJoules

/-! ## Lattice, melting mechanism, and primary-raster vocabulary -/

/-- Physical composition of the solid. -/
inductive SolidComposition where
  | monatomic
  | other
  deriving DecidableEq, Repr

/-- Crystal-lattice class used by the physical model. -/
inductive LatticeKind where
  | simpleCubic
  | other
  deriving DecidableEq, Repr

/-- Qualitative binding regime stated in the problem. -/
inductive BindingRegime where
  | weaklyBound
  | other
  deriving DecidableEq, Repr

/-- Where the latent heat supplied during fusion is deposited. -/
inductive FusionEnergyDestination where
  | breakingLatticeBonds
  | other
  deriving DecidableEq, Repr

/-- Geometric arrangement visible in the supplied raster. -/
inductive FigureArrangement where
  | threeDimensionalSimpleCubicLayers
  | other
  deriving DecidableEq, Repr

/-- Glyph used to depict an atom site. -/
inductive SiteGlyph where
  | sphere
  | other
  deriving DecidableEq, Repr

/-- Colors occurring in the raster. -/
inductive FigureColor where
  | yellow
  | black
  | other
  deriving DecidableEq, Repr

/-- Stroke used to depict a bond. -/
inductive BondStroke where
  | straightLine
  | other
  deriving DecidableEq, Repr

/--
Literal qualitative data in the primary raster. The Boolean fields record
visible presentation facts, not numerical bond counts or thermodynamic
conclusions.
-/
structure CubicLatticeFigure where
  arrangement : FigureArrangement
  siteGlyph : SiteGlyph
  siteColor : FigureColor
  bondStroke : BondStroke
  bondColor : FigureColor
  sitesUniformlySpaced : Bool
  nearestNeighborConnectionsShown : Bool
  containsTextLabels : Bool
  containsOtherObjects : Bool

/--
Independent physical data for the solid. `Atom` indexes a representative
finite bulk sample, and `latticeBondGraph` is its loopless undirected bond
network. The latent heat is an independent quantity, not a definition made
from an answer choice.
-/
structure MonatomicCubicSolidSetup
    (Atom : Type) (molarEnergyScale : MolarEnergyScale) where
  composition : SolidComposition
  latticeKind : LatticeKind
  bindingRegime : BindingRegime
  latticeBondGraph : SimpleGraph Atom
  bindingEnergyPerBond : DimEnergy
  atomsPerMole : ℝ
  latentHeatOfFusion : molarEnergyScale.Quantity
  fusionEnergyDestination : FusionEnergyDestination
  figure : CubicLatticeFigure

/-! ## Assumptions: scenario, figure evidence, calibrations, and laws -/

/--
The prose-level physical scenario. Six-regularity is the bulk
nearest-neighbour idealization. Since `SimpleGraph` is loopless and
undirected, one bond joins two distinct sites and is not double-oriented.
-/
structure MatchesWeaklyBoundSimpleCubicScenario
    {Atom : Type} [Fintype Atom]
    {molarEnergyScale : MolarEnergyScale}
    (setup : MonatomicCubicSolidSetup Atom molarEnergyScale)
    [DecidableRel setup.latticeBondGraph.Adj] : Prop where
  compositionIsMonatomic : setup.composition = .monatomic
  latticeIsSimpleCubic : setup.latticeKind = .simpleCubic
  bindingIsWeak : setup.bindingRegime = .weaklyBound
  eachBulkAtomHasSixNeighbors :
    setup.latticeBondGraph.IsRegularOfDegree 6
  fusionEnergyBreaksBonds :
    setup.fusionEnergyDestination = .breakingLatticeBonds

/--
Facts read from the primary raster. In particular, the image has no text,
numeric answer, or thermodynamic annotation.
-/
structure MatchesSuppliedCubicLatticeFigure
    {Atom : Type} {molarEnergyScale : MolarEnergyScale}
    (setup : MonatomicCubicSolidSetup Atom molarEnergyScale) : Prop where
  arrangementIsCubicLayers :
    setup.figure.arrangement = .threeDimensionalSimpleCubicLayers
  atomSitesAreSpheres : setup.figure.siteGlyph = .sphere
  atomSitesAreYellow : setup.figure.siteColor = .yellow
  bondsAreStraightLines : setup.figure.bondStroke = .straightLine
  bondsAreBlack : setup.figure.bondColor = .black
  sitesAreUniformlySpaced : setup.figure.sitesUniformlySpaced = true
  nearestNeighborConnectionsVisible :
    setup.figure.nearestNeighborConnectionsShown = true
  noTextLabels : setup.figure.containsTextLabels = false
  noOtherObjects : setup.figure.containsOtherObjects = false

/--
Stated numerical inputs at explicit unit-readout boundaries. The bond energy
is `3.4 * 10⁻³ eV`, and the second field is the exact number of atoms per
mole. Neither field mentions the requested latent heat.
-/
structure HasStatedBondAndMoleCalibrations
    {Atom : Type} {molarEnergyScale : MolarEnergyScale}
    (setup : MonatomicCubicSolidSetup Atom molarEnergyScale) : Prop where
  bindingEnergyReadout :
    energyInElectronVolts setup.bindingEnergyPerBond = (34 : ℝ) / 10000
  avogadroReadout :
    setup.atomsPerMole = (602214076 : ℝ) * 10 ^ 15

/-- Positivity and non-vacuity conditions for a physical bulk sample. -/
structure HasPhysicalCubicSolidParameters
    {Atom : Type} [Fintype Atom]
    {molarEnergyScale : MolarEnergyScale}
    (setup : MonatomicCubicSolidSetup Atom molarEnergyScale) : Prop where
  representativeBulkSampleNonempty : 0 < Fintype.card Atom
  bindingEnergyPositive : 0 < energyInJoules setup.bindingEnergyPerBond
  atomsPerMolePositive : 0 < setup.atomsPerMole
  latentHeatPositive :
    0 < molarEnergyScale.inJoulesPerMole setup.latentHeatOfFusion

/--
General bond-breaking energy accounting for one mole. Multiplication by the
number of atoms in the representative bulk sample avoids assuming the desired
three-bonds-per-atom conclusion; that relation must be derived from
six-regularity by the handshaking lemma.
-/
structure SatisfiesFusionBondBreakingLaw
    {Atom : Type} [Fintype Atom]
    {molarEnergyScale : MolarEnergyScale}
    (setup : MonatomicCubicSolidSetup Atom molarEnergyScale)
    [DecidableRel setup.latticeBondGraph.Adj] : Prop where
  fusionEnergyBalance :
    (Fintype.card Atom : ℝ) *
          molarEnergyScale.inJoulesPerMole setup.latentHeatOfFusion =
      (setup.latticeBondGraph.edgeFinset.card : ℝ) * setup.atomsPerMole *
        energyInJoules setup.bindingEnergyPerBond

/-! ## Derived bond count, displayed answers, and current target -/

/--
The hint's bond-count conclusion: a finite six-regular bulk model has three
times as many undirected bonds as atom sites.
-/
lemma bulkBondCount_eq_three_mul_atomCount
    {Atom : Type} [Fintype Atom]
    (graph : SimpleGraph Atom)
    [DecidableRel graph.Adj]
    (hSixRegular : graph.IsRegularOfDegree 6) :
    graph.edgeFinset.card = 3 * Fintype.card Atom := by
  have hDegreeSum := graph.sum_degrees_eq_twice_card_edges
  simp only [hSixRegular.degree_eq, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hDegreeSum
  norm_num at hDegreeSum ⊢
  omega

/--
The energy balance and derived bond count express molar latent heat as three
bond energies per atom times the number of atoms in one mole.
-/
lemma latentHeat_eq_three_bonds_per_atom
    {Atom : Type} [Fintype Atom]
    {molarEnergyScale : MolarEnergyScale}
    (setup : MonatomicCubicSolidSetup Atom molarEnergyScale)
    [DecidableRel setup.latticeBondGraph.Adj]
    (hScenario : MatchesWeaklyBoundSimpleCubicScenario setup)
    (hPhysical : HasPhysicalCubicSolidParameters setup)
    (hLaw : SatisfiesFusionBondBreakingLaw setup) :
    molarEnergyScale.inJoulesPerMole setup.latentHeatOfFusion =
      3 * setup.atomsPerMole * energyInJoules setup.bindingEnergyPerBond := by
  have hBondCount :
      setup.latticeBondGraph.edgeFinset.card = 3 * Fintype.card Atom :=
    bulkBondCount_eq_three_mul_atomCount
      setup.latticeBondGraph hScenario.eachBulkAtomHasSixNeighbors
  have hCardPositive : (0 : ℝ) < Fintype.card Atom := by
    exact_mod_cast hPhysical.representativeBulkSampleNonempty
  have hBalance := hLaw.fusionEnergyBalance
  rw [hBondCount] at hBalance
  apply mul_left_cancel₀ (ne_of_gt hCardPositive)
  calc
    (Fintype.card Atom : ℝ) *
          molarEnergyScale.inJoulesPerMole setup.latentHeatOfFusion =
        ((3 * Fintype.card Atom : ℕ) : ℝ) * setup.atomsPerMole *
          energyInJoules setup.bindingEnergyPerBond := hBalance
    _ = (Fintype.card Atom : ℝ) *
          (3 * setup.atomsPerMole *
            energyInJoules setup.bindingEnergyPerBond) := by
      push_cast
      ring

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed latent heats of fusion, read in joules per mole. -/
def displayedLatentHeatInJoulesPerMole : AnswerChoice → ℝ
  | .A => 960
  | .B => 970
  | .C => 990
  | .D => 980

/-- The source dataset records choice D; this metadata is not a premise. -/
def recordedAnswer : AnswerChoice := .D

/--
A displayed choice is uniquely closest to the physical molar-latent-heat
readout. Strict comparison is required only against different labels.
-/
def IsUniqueClosestDisplayedChoice
    {molarEnergyScale : MolarEnergyScale}
    (latentHeat : molarEnergyScale.Quantity)
    (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |molarEnergyScale.inJoulesPerMole latentHeat -
        displayedLatentHeatInJoulesPerMole choice| <
      |molarEnergyScale.inJoulesPerMole latentHeat -
        displayedLatentHeatInJoulesPerMole other|

/--
Using three bonds per atom, the stated bond energy, Physlib's exact eV-to-J
conversion, and the Avogadro readout gives about `984.15 J/mol`. Thus the
latent heat is within `5 J/mol` of `980 J/mol`, and D is the unique closest
displayed estimate.

This declaration formalizes `thm:physics:phyx_mini_0625:target`.
-/
theorem problem_phyx_mini_0625
    {Atom : Type} [Fintype Atom]
    {molarEnergyScale : MolarEnergyScale}
    (setup : MonatomicCubicSolidSetup Atom molarEnergyScale)
    [DecidableRel setup.latticeBondGraph.Adj]
    (hScenario : MatchesWeaklyBoundSimpleCubicScenario setup)
    (hFigure : MatchesSuppliedCubicLatticeFigure setup)
    (hCalibrations : HasStatedBondAndMoleCalibrations setup)
    (hPhysical : HasPhysicalCubicSolidParameters setup)
    (hLaw : SatisfiesFusionBondBreakingLaw setup) :
    |molarEnergyScale.inJoulesPerMole setup.latentHeatOfFusion - 980| < 5 ∧
      IsUniqueClosestDisplayedChoice setup.latentHeatOfFusion .D := by
  have hLatentHeat :=
    latentHeat_eq_three_bonds_per_atom setup hScenario hPhysical hLaw
  have hElectronVolt :
      electronVoltInJoules = (1602176634 / 10 ^ 28 : ℝ) := by
    norm_num [electronVoltInJoules, energyInJoules,
      DimEnergy.electronVolt, CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self]
  have hElectronVoltNonzero : electronVoltInJoules ≠ 0 := by
    rw [hElectronVolt]
    norm_num
  have hBindingEnergy :
      energyInJoules setup.bindingEnergyPerBond =
        ((34 : ℝ) / 10000) * electronVoltInJoules := by
    apply (div_eq_iff hElectronVoltNonzero).mp
    simpa [energyInElectronVolts] using
      hCalibrations.bindingEnergyReadout
  rw [hCalibrations.avogadroReadout, hBindingEnergy, hElectronVolt] at hLatentHeat
  norm_num at hLatentHeat
  constructor
  · rw [hLatentHeat]
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · unfold IsUniqueClosestDisplayedChoice
    intro other hOther
    fin_cases other <;>
      norm_num [displayedLatentHeatInJoulesPerMole] at hOther <;>
      norm_num [displayedLatentHeatInJoulesPerMole, hLatentHeat,
        abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0625
