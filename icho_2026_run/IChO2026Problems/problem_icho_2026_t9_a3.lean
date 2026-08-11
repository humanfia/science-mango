import IChO2026Chem
import Mathlib

/-!
# IChO 2026 T9-A3: ring size and stereocentre count of macrocycle X

The source drawing starts from β-cyclodextrin, hence seven
α-D-glucopyranoside repeats.  This model begins with the complete seven-site
backbone graph relevant to each repeat, rather than postulating a five-member
ring inventory or a three-member stereochemical inventory.

The precursor graph contains the pyranose cycle

`C1-O5-C5-C4-C3-C2-C1`

and the inter-repeat glycosidic path

`C4-O(α1→4)-C1(next repeat)`.

The displayed periodate operation deletes every C2-C3 bond.  Ring atoms are
then computed from the post-cleavage graph by the structural predicate
"post-reaction backbone degree at least two"; the cleaved C2 and C3 termini
have degree one and are filtered out.  Stereochemical counting starts from
the source-backed tetrahedral geometry of C1-C5.  Cleavage followed by
borohydride reduction replaces the deleted carbon neighbour at C2 and C3 by
an additional hydrogen, so a generic four-distinct-ligands test rejects those
two sites.  It retains C1, C4, and C5, with C1 classified as the pseudochiral
acetal specified by the official solution.
-/

namespace IChO2026Problems.T9A3

/-- Operations printed above the reaction arrow leading to `X`. -/
private inductive MacrocycleXSynthesisOperation where
  | periodateCleavageOfVicinalDiol
  | borohydrideReductionInWater
  | acetylationWithAceticAnhydrideInPyridine
  deriving DecidableEq, Repr

/--
All heavy-atom sites needed to reconstruct the glucopyranoside backbone in
the source image.  `glycosidicOxygenO14` is the oxygen of the α(1→4) link to
the following repeat.
-/
private inductive GlucopyranosideBackboneSite where
  | anomericCarbonC1
  | vicinalDiolCarbonC2
  | vicinalDiolCarbonC3
  | glycosidicCarbonC4
  | ringCarbonC5
  | pyranoseRingOxygenO5
  | glycosidicOxygenO14
  deriving DecidableEq, Repr, Fintype

/-- The β-CD subscript seven in the source supplies the repeat carrier. -/
private abbrev BetaCDRepeat := Fin 7

/-- An atom is identified by its repeat and its chemical site in that repeat. -/
private abbrev BackboneAtom := BetaCDRepeat × GlucopyranosideBackboneSite

/-- Cyclic successor of a repeat index. -/
private def nextRepeat (repeatIndex : BetaCDRepeat) : BetaCDRepeat :=
  ⟨(repeatIndex.val + 1) % 7, Nat.mod_lt _ (by norm_num)⟩

/--
The undirected bonds drawn inside one intact glucopyranoside repeat, including
the C4-glycosidic-oxygen half of the inter-repeat linkage.
-/
private def bondedInsidePrecursorRepeat :
    GlucopyranosideBackboneSite → GlucopyranosideBackboneSite → Bool
  | .anomericCarbonC1, .pyranoseRingOxygenO5 => true
  | .pyranoseRingOxygenO5, .anomericCarbonC1 => true
  | .pyranoseRingOxygenO5, .ringCarbonC5 => true
  | .ringCarbonC5, .pyranoseRingOxygenO5 => true
  | .ringCarbonC5, .glycosidicCarbonC4 => true
  | .glycosidicCarbonC4, .ringCarbonC5 => true
  | .glycosidicCarbonC4, .vicinalDiolCarbonC3 => true
  | .vicinalDiolCarbonC3, .glycosidicCarbonC4 => true
  | .vicinalDiolCarbonC3, .vicinalDiolCarbonC2 => true
  | .vicinalDiolCarbonC2, .vicinalDiolCarbonC3 => true
  | .vicinalDiolCarbonC2, .anomericCarbonC1 => true
  | .anomericCarbonC1, .vicinalDiolCarbonC2 => true
  | .glycosidicCarbonC4, .glycosidicOxygenO14 => true
  | .glycosidicOxygenO14, .glycosidicCarbonC4 => true
  | _, _ => false

/-- Complete source-backed precursor bonding, including `O(α1→4)-C1(next)`. -/
private def precursorBonded (left right : BackboneAtom) : Bool :=
  (decide (left.1 = right.1) && bondedInsidePrecursorRepeat left.2 right.2) ||
    (decide (right.1 = nextRepeat left.1) &&
      decide (left.2 = .glycosidicOxygenO14) &&
        decide (right.2 = .anomericCarbonC1)) ||
    (decide (left.1 = nextRepeat right.1) &&
      decide (right.2 = .glycosidicOxygenO14) &&
        decide (left.2 = .anomericCarbonC1))

/-- A finite molecular-backbone graph on the complete atom carrier. -/
private structure BackboneGraph where
  atoms : Finset BackboneAtom
  bonded : BackboneAtom → BackboneAtom → Bool

/-- The intact β-cyclodextrin precursor graph read from the source template. -/
private def betaCyclodextrinPrecursorGraph : BackboneGraph where
  atoms := Finset.univ
  bonded := precursorBonded

/--
Generic graph operation that deletes every bond satisfying a reaction rule.
-/
private def BackboneGraph.deleteBonds
    (graph : BackboneGraph) (deletedByReaction : BackboneAtom → BackboneAtom → Bool) :
    BackboneGraph where
  atoms := graph.atoms
  bonded := fun left right => graph.bonded left right && !deletedByReaction left right

/-- The NaIO₄ rule: delete the C2-C3 vicinal-diol bond in every repeat. -/
private def periodateCleavedBond (left right : BackboneAtom) : Bool :=
  decide (left.1 = right.1) &&
    (decide (left.2 = .vicinalDiolCarbonC2) &&
        decide (right.2 = .vicinalDiolCarbonC3) ||
      decide (left.2 = .vicinalDiolCarbonC3) &&
        decide (right.2 = .vicinalDiolCarbonC2))

/-- Connectivity after periodate cleavage; reduction does not reconnect C2-C3. -/
private def macrocycleXBackboneGraph : BackboneGraph :=
  betaCyclodextrinPrecursorGraph.deleteBonds periodateCleavedBond

/-- Neighbours are computed from a graph, not supplied as an answer inventory. -/
private def BackboneGraph.neighbours
    (graph : BackboneGraph) (atom : BackboneAtom) : Finset BackboneAtom :=
  graph.atoms.filter fun candidate => graph.bonded atom candidate

/-- Heavy-backbone degree in a molecular graph. -/
private def BackboneGraph.degree (graph : BackboneGraph) (atom : BackboneAtom) : ℕ :=
  (graph.neighbours atom).card

/--
For this cleaved glucopyranoside graph, atoms retained on the cyclic backbone
are exactly those with at least two post-reaction backbone neighbours.
-/
private def hasRetainedMacrocyclicDegree (atom : BackboneAtom) : Bool :=
  decide (2 ≤ macrocycleXBackboneGraph.degree atom)

/-- Ring-atom inventory obtained by filtering the complete 49-atom carrier. -/
private def macrocycleXRingAtoms : Finset BackboneAtom :=
  macrocycleXBackboneGraph.atoms.filter fun atom =>
    hasRetainedMacrocyclicDegree atom = true

/-- Elements needed for the tetrahedral-ligand test. -/
private inductive ChemicalElement where
  | carbon
  | oxygen
  deriving DecidableEq, Repr

/-- Source-backed tetrahedral environment before periodate cleavage. -/
private structure TetrahedralLigandGeometry where
  element : ChemicalElement
  isTetrahedral : Bool
  hydrogenLigandCount : ℕ
  nonHydrogenLigandsPairwiseDistinct : Bool

/--
In the glucopyranoside structure, C1-C5 are tetrahedral carbons with one
hydrogen and three distinct non-hydrogen ligand paths.  The two oxygens are
not candidate carbon stereocentres.
-/
private def precursorLigandGeometry :
    GlucopyranosideBackboneSite → TetrahedralLigandGeometry
  | .anomericCarbonC1 => ⟨.carbon, true, 1, true⟩
  | .vicinalDiolCarbonC2 => ⟨.carbon, true, 1, true⟩
  | .vicinalDiolCarbonC3 => ⟨.carbon, true, 1, true⟩
  | .glycosidicCarbonC4 => ⟨.carbon, true, 1, true⟩
  | .ringCarbonC5 => ⟨.carbon, true, 1, true⟩
  | .pyranoseRingOxygenO5 => ⟨.oxygen, false, 0, false⟩
  | .glycosidicOxygenO14 => ⟨.oxygen, false, 0, false⟩

/-- Number of heavy-atom bonds removed at a given atom by the reaction. -/
private def deletedIncidentBondCount (atom : BackboneAtom) : ℕ :=
  betaCyclodextrinPrecursorGraph.degree atom - macrocycleXBackboneGraph.degree atom

/--
Periodate cleavage and borohydride reduction replace each deleted C-C ligand
at the cleavage termini by hydrogen.  This generic transformation derives two
hydrogen ligands at C2/C3 while leaving C1/C4/C5 at one.
-/
private def ligandGeometryAfterCleavageAndReduction
    (atom : BackboneAtom) : TetrahedralLigandGeometry :=
  let precursor := precursorLigandGeometry atom.2
  { precursor with
    hydrogenLigandCount := precursor.hydrogenLigandCount + deletedIncidentBondCount atom }

/-- Generic criterion for four distinguishable ligands at a tetrahedral carbon. -/
private def TetrahedralLigandGeometry.hasFourDistinctLigands
    (geometry : TetrahedralLigandGeometry) : Bool :=
  decide (geometry.element = .carbon) &&
    geometry.isTetrahedral &&
      decide (geometry.hydrogenLigandCount ≤ 1) &&
        geometry.nonHydrogenLigandsPairwiseDistinct

/-- Classification used by the rubric; the C1 acetal is explicitly pseudochiral. -/
private inductive CountedStereochemicalKind where
  | stereogenicCarbon
  | pseudochiralAcetal
  deriving DecidableEq, Repr

/--
Classify only atoms passing the generic ligand test.  The official solution's
pseudochiral qualification changes the label at C1, not whether it is counted.
-/
private def countedStereochemicalKind?
    (atom : BackboneAtom) : Option CountedStereochemicalKind :=
  if (ligandGeometryAfterCleavageAndReduction atom).hasFourDistinctLigands then
    if atom.2 = .anomericCarbonC1 then some .pseudochiralAcetal
    else some .stereogenicCarbon
  else none

/-- Stereochemical inventory filtered from the same complete atom carrier. -/
private def macrocycleXCountedStereochemicalAtoms : Finset BackboneAtom :=
  macrocycleXBackboneGraph.atoms.filter fun atom =>
    (countedStereochemicalKind? atom).isSome = true

/-- Reaction-product data relevant to the two requested outputs. -/
private structure CyclodextrinDerivedMacrocycle where
  synthesisOperations : List MacrocycleXSynthesisOperation
  precursorGraph : BackboneGraph
  productGraph : BackboneGraph
  macrocyclicRingAtoms : Finset BackboneAtom
  countedStereochemicalAtoms : Finset BackboneAtom

/-- Macrocycle `X`, assembled by applying the displayed operations to β-CD. -/
private def macrocycleX : CyclodextrinDerivedMacrocycle where
  synthesisOperations :=
    [ .periodateCleavageOfVicinalDiol,
      .borohydrideReductionInWater,
      .acetylationWithAceticAnhydrideInPyridine ]
  precursorGraph := betaCyclodextrinPrecursorGraph
  productGraph := macrocycleXBackboneGraph
  macrocyclicRingAtoms := macrocycleXRingAtoms
  countedStereochemicalAtoms := macrocycleXCountedStereochemicalAtoms

/-- Ring size is read from the graph-derived atom inventory. -/
private def CyclodextrinDerivedMacrocycle.ringSize
    (macrocycle : CyclodextrinDerivedMacrocycle) : ℕ :=
  macrocycle.macrocyclicRingAtoms.card

/-- The rubric's count includes both ordinary and pseudochiral classified sites. -/
private def CyclodextrinDerivedMacrocycle.stereocentreCount
    (macrocycle : CyclodextrinDerivedMacrocycle) : ℕ :=
  macrocycle.countedStereochemicalAtoms.card

/--
Auditable reaction diagnostic: deleted-bond incidence adds one hydrogen only
at C2 and C3; all other relevant sites keep their precursor hydrogen count.
-/
private theorem cleavage_reduction_geometry_diagnostic :
    ∀ repeatIndex : BetaCDRepeat,
      (ligandGeometryAfterCleavageAndReduction
          (repeatIndex, .anomericCarbonC1)).hydrogenLigandCount = 1 ∧
      (ligandGeometryAfterCleavageAndReduction
          (repeatIndex, .vicinalDiolCarbonC2)).hydrogenLigandCount = 2 ∧
      (ligandGeometryAfterCleavageAndReduction
          (repeatIndex, .vicinalDiolCarbonC3)).hydrogenLigandCount = 2 ∧
      (ligandGeometryAfterCleavageAndReduction
          (repeatIndex, .glycosidicCarbonC4)).hydrogenLigandCount = 1 ∧
      (ligandGeometryAfterCleavageAndReduction
          (repeatIndex, .ringCarbonC5)).hydrogenLigandCount = 1 := by
  decide +kernel

/-- Computation from the full post-reaction graph, not a five-item definition. -/
private theorem macrocycleXRingAtoms_card : macrocycleXRingAtoms.card = 35 := by
  decide +kernel

/-- Computation from transformed ligand geometries, not a three-item definition. -/
private theorem macrocycleXCountedStereochemicalAtoms_card :
    macrocycleXCountedStereochemicalAtoms.card = 21 := by
  decide +kernel

/--
T9-A3.  Applying periodate cleavage/reduction to the complete β-CD precursor
graph gives a 35-membered retained macrocycle and 21 counted stereochemical
centres, including the seven pseudochiral C1 acetals.
-/
theorem macrocycleX_ring_size_and_stereocentre_count :
    macrocycleX.ringSize = 35 ∧ macrocycleX.stereocentreCount = 21 := by
  exact ⟨macrocycleXRingAtoms_card, macrocycleXCountedStereochemicalAtoms_card⟩

end IChO2026Problems.T9A3
