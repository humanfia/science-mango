import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem T9, subquestion 9.3 — ring size and
stereocentre count of macrocycle X

## Source

58th International Chemistry Olympiad, Tashkent, Uzbekistan, 2026.
Problem T9 (Cyclodextrin Chemistry), current subquestion 9.3 (8.0 pt):

> **Determine** the ring size, `rs`, of macrocycle **X**.
> **Give** the number of stereocentres, `sc`, in **X**.

Visual evidence inspected:
* `icho_2026_source/image/T9_page-1.png` — CD family table (α-, β-, γ-CD =
  6, 7, 8 α-D-glucopyranoside units), the β-CD repeat-unit bracket with
  subscript `n`, and the full `n = 7` β-CD structure.
* `icho_2026_source/image/T9_page-2.png` — the reaction scheme
  β-CD (bracket subscript `7`) → K (1. TsCl, 7 equiv., Py; 2. NaOH, H₂O,
  60 °C) → X (1. NaIO₄; 2. NaBH₄, H₂O; 3. Ac₂O, Py), and the boxed
  statement of 9.3.

## Chemistry behind the formalization

* **Shared context (problem text, page 1).** Cyclodextrins are cyclic
  oligosaccharides of α-D-glucopyranose units joined by α-1,4-glycosidic
  bonds; α-, β-, γ-CD contain 6, 7, 8 units respectively.  The T9 scheme
  starts from **β-CD** and converts it into **K** and then into **X**.

* **Previous part T9-A2 (natural-language prerequisite only; the current
  target is not assumed).**  In K a new ring has formed on every
  glucopyranose unit with the bridging atoms in axial positions — the
  3,6-anhydro bridge installed by intramolecular displacement of the C6
  tosylate by the C3 alkoxide — so that exactly one OH group (at C2)
  remains free per glucopyranoside unit.

* **The transformation K → X.**  NaIO₄ cleaves the only oxidizable vicinal
  oxygen motif of K, the C2(OH)–C3(O-bridge) hydroxy-ether: the C2–C3
  bond breaks and, since C3 cannot support both the bridge oxygen and a
  carbonyl (valence), the C3–O(anhydro) bond breaks as well, releasing the
  bridge oxygen as the C6 hydroxyl.  NaBH₄ then reduces the two resulting
  aldehydes (at C2 and C3) to hydroxymethyl groups, installing a new
  hydroxyl oxygen on C3; Ac₂O/Py caps the free hydroxyls as acetates.
  The marking scheme describes the repeat unit of X as a
  *meso*-butanetetrol/glycolaldehyde acetal unit, states that the
  macrocyclic ring contains five atoms per repeat unit, that the number of
  asymmetric atoms per unit drops to three, and that one of them (the
  acetal carbon) is pseudochiral, making the macrocycle achiral overall.

## Assumption/target split

*Assumptions (sourced structural data, encoded as definitions).*
(i) β-CD — and hence X, which inherits one repeat unit per glucopyranoside
unit through the C2–C3 cleavage (no glycosidic bond is touched) — is a
cyclic heptamer (`betaCDUnits = 7`, problem text and scheme subscript).
(ii) The complete heavy-atom/bond graph of one repeat unit of the
precursor K, on the explicit precursor vertex carrier `PrecursorAtom`
(all of C1–C6, the ring oxygen O5, the 3,6-anhydro bridge oxygen, the
inter-unit glycosidic oxygen, the free C2 hydroxyl — and nothing else),
with atom labels `labelK` and the α-D-glucose-derived tetrahedral
configuration data `configK` (all five stereocentres of the
3,6-anhydroglucose unit).
(iii) The NaIO₄/NaBH₄ transformation, encoded as data acting on the
precursor graph: the embedded precursor bonds minus `cleavedBonds` plus
`installedBonds` give the post-reaction unit bond list `bondsX`, through
which the product-only C3 hydroxyl oxygen `OHydroxylC3` enters the
molecule; ligand data `labelX` and stereochemical references `configX` are
likewise transforms of the precursor data, machine-checked by
`labelX_eq_labelK_transform` and `configX_eq_configK_transform`.
The acetyl caps of the final Ac₂O/Py step are suppressed (see `labelX`):
they add only exocyclic achiral leaves and cannot change `rs` or `sc`.

*Derived, not assumed.*  Ring membership is graph connectivity
(`IsRingAtom`: the atom lies on a cycle of the molecular graph), and
stereogenicity is a general four-distinct-ligands predicate
(`IsStereocentre`: ligand classes are orbits of label- and
configuration-preserving graph automorphisms fixing the centre).  The
transformation retains stereochemical *reference* labels only at C4 and
C5 (the meso branch labels) and deliberately leaves the acetal carbon C1
unlabelled: its membership in the stereocentre set, and its
pseudochirality, are derived solely from the difference between
constitutional and stereochemical ligand automorphisms
(`acetalCarbon_isPseudochiralCentre`).  The five ring atoms and three
stereocentres per unit are theorems (`ringAtomsOfUnit_eq_five`,
`stereocentresOfUnit_eq_three`), as is the achirality of the macrocycle.

*Target (the numerals 35 and 21 appear only here).*
`ringSizeX = 35 ∧ stereocentresX = 21`.
-/

namespace IChO2026.T9.A3

/-- The heavy-atom carrier of the repeat unit of **X**, atom names
following the parent glucose numbering.  Every atom except `OHydroxylC3`
is already present in the precursor K; `OHydroxylC3` is the hydroxyl
oxygen installed on C3 by the NaIO₄/NaBH₄ sequence and is excluded from
the precursor carrier `PrecursorAtom`. -/
inductive UnitAtom : Type where
  /-- Anomeric carbon C1: in K the glycosidic acetal carbon; in X the
  glycolaldehyde-derived acetal carbon of the repeat unit. -/
  | C1
  /-- Carbon C2, bearing the single free hydroxyl of K; cleaved from C3 by
  NaIO₄ and reduced by NaBH₄ to a hydroxymethyl substituent on C1. -/
  | C2
  /-- Carbon C3, carrying the anhydro bridge oxygen in K; cleaved from C2
  and reduced to a hydroxymethyl substituent on C4 in X. -/
  | C3
  /-- Carbon C4, bearing the glycosidic bond from the previous unit;
  retained stereocentre of the butanetetrol half of X's repeat unit. -/
  | C4
  /-- Carbon C5, bonded to the ring oxygen O5; retained stereocentre of
  the butanetetrol half of X's repeat unit. -/
  | C5
  /-- Carbon C6, the methylene of the 3,6-anhydro bridge in K; a
  hydroxymethyl substituent on C5 in X. -/
  | C6
  /-- The pyranose ring oxygen O5, bridging C1 and C5; in X it is one of
  the two acetal oxygens of the repeat unit. -/
  | O5
  /-- The 3,6-anhydro bridge oxygen of K (bonded to C3 and C6); released
  by the periodate cleavage to become the C6 hydroxyl oxygen of X. -/
  | OAnhydro
  /-- The inter-unit α-1,4-glycosidic oxygen: bonded to this unit's C1
  and to the next unit's C4.  A cyclic `n`-mer has exactly `n` glycosidic
  linkages, so one glycosidic oxygen per unit partitions these atoms. -/
  | OGly
  /-- The oxygen of the single free hydroxyl group of K, at C2; retained
  as the C2 hydroxymethyl hydroxyl of X. -/
  | OHydroxylC2
  /-- The hydroxyl oxygen installed on C3 by the NaIO₄/NaBH₄ sequence
  (the C3 aldehyde oxygen); not part of the precursor K. -/
  | OHydroxylC3
  deriving DecidableEq, Repr, BEq, Fintype

open UnitAtom

/-- Presence in the precursor K: every atom of the shared carrier except
the product-only C3 hydroxyl oxygen. -/
def presentInK : UnitAtom → Bool
  | .OHydroxylC3 => false
  | _ => true

/-- The precursor vertex carrier: exactly the atoms of one repeat unit of
K.  The C3 hydroxyl oxygen of X is *not* a vertex of the precursor graph;
it is introduced by the transformation (`bondsX`). -/
abbrev PrecursorAtom := {a : UnitAtom // presentInK a = true}

instance : BEq PrecursorAtom := ⟨fun a b => a.1 == b.1⟩

/-- Embed an atom known to be present in K into the precursor carrier. -/
abbrev pk (a : UnitAtom) (h : presentInK a = true := by decide) : PrecursorAtom := ⟨a, h⟩

/-- Undirected membership test for a bond list. -/
def memBond {α : Type} [BEq α] (l : List (α × α)) (a b : α) : Bool :=
  l.contains (a, b) || l.contains (b, a)

/-- The undirected bond list of one repeat unit of the precursor K, over
the precursor carrier: the six pyranose-ring bonds, the three
3,6-anhydro-bridge bonds, the intra-unit half of the α-1,4-glycosidic
bond (C1–OGly), and the free C2 hydroxyl.  This is the complete
per-repeat precursor atom/bond graph; the inter-unit half of the
glycosidic linkage (OGly–C4 of the next unit) is supplied by
`macrocycleAdj` and is unchanged by the K → X sequence. -/
def precursorBonds : List (PrecursorAtom × PrecursorAtom) :=
  [ -- pyranose ring: O5–C1–C2–C3–C4–C5–O5
    (pk C1, pk C2), (pk C2, pk C3), (pk C3, pk C4), (pk C4, pk C5),
    (pk C5, pk O5), (pk O5, pk C1),
    -- 3,6-anhydro bridge: C3–O–C6–C5 (the new ring formed in K, T9-A2)
    (pk C3, pk OAnhydro), (pk OAnhydro, pk C6), (pk C6, pk C5),
    -- α-glycosidic bond, intra-unit half
    (pk C1, pk OGly),
    -- the one free hydroxyl of K
    (pk C2, pk OHydroxylC2) ]

/-- The intra-unit bond relation of the precursor K. -/
def precursorBonded (a b : PrecursorAtom) : Bool := memBond precursorBonds a b

/-- The precursor bond relation is symmetric (it is an undirected graph). -/
theorem precursorBonded_symm :
    ∀ a b : PrecursorAtom, precursorBonded a b = precursorBonded b a := by decide

/-- No atom of K is bonded to itself. -/
theorem precursorBonded_irrefl : ∀ a : PrecursorAtom, precursorBonded a a = false := by
  decide

/-- The molecular graph of one repeat unit of the precursor K on its
heavy atoms. -/
def precursorGraph : SimpleGraph PrecursorAtom where
  Adj a b := precursorBonded a b = true
  symm := ⟨fun a b h => by rw [precursorBonded_symm]; exact h⟩
  loopless := ⟨fun a h => by rw [precursorBonded_irrefl] at h; exact Bool.false_ne_true h⟩

/-- The precursor K really contains the anhydro bridge and the free C2
hydroxyl (the structural content of T9-A2), and both later-cleaved bonds
are genuinely present: the transformation below is not vacuous. -/
theorem precursor_motifs_present :
    precursorBonded (pk C3) (pk OAnhydro) = true ∧
    precursorBonded (pk OAnhydro) (pk C6) = true ∧
    precursorBonded (pk C2) (pk OHydroxylC2) = true ∧
    precursorBonded (pk C2) (pk C3) = true := by decide

/-- Every precursor atom survives the K → X sequence: the vertex embedding
of the transformation (periodate cleavage removes no heavy atom). -/
def embedK : PrecursorAtom → UnitAtom := Subtype.val

/-- The bonds broken by the NaIO₄ step: the C2–C3 bond of the
hydroxy-ether motif, and the C3–OAnhydro bond — the α-alkoxy carbon C3
cannot keep its ether oxygen while becoming an aldehyde (valence), so the
bridge oxygen is released as the C6 hydroxyl. -/
def cleavedBonds : List (UnitAtom × UnitAtom) := [(C2, C3), (C3, OAnhydro)]

/-- The bond installed by the NaBH₄ step: reduction of the C3 aldehyde
gives the C3 hydroxymethyl group with its new hydroxyl oxygen.  This is
where the vertex `OHydroxylC3` enters the molecule.  (The C2 aldehyde
reuses `OHydroxylC2`, already present in K.) -/
def installedBonds : List (UnitAtom × UnitAtom) := [(C3, OHydroxylC3)]

/-- The intra-unit bond list of **X**, produced by the graph
transformation: the embedded precursor bonds with the cleaved bonds
removed, plus the reduction-installed C3 hydroxyl bond. -/
def bondsX : List (UnitAtom × UnitAtom) :=
  (precursorBonds.map (fun e => (embedK e.1, embedK e.2))).filter
    (fun e => !memBond cleavedBonds e.1 e.2) ++ installedBonds

/-- The intra-unit bond relation of X. -/
def bondedX (a b : UnitAtom) : Bool := memBond bondsX a b

/-- The unit bond relation of X is symmetric (it is an undirected graph). -/
theorem bondedX_symm : ∀ a b : UnitAtom, bondedX a b = bondedX b a := by decide

/-- No atom of X is bonded to itself. -/
theorem bondedX_irrefl : ∀ a : UnitAtom, bondedX a a = false := by decide

/-- The C3 hydroxyl oxygen is absent from the precursor carrier and enters
only through the transformation. -/
theorem c3_hydroxyl_absent_from_precursor : presentInK OHydroxylC3 = false := rfl

/-- After the transformation the cleaved bonds are gone: the C2–C3 bond
and the C3–bridge-oxygen bond no longer exist. -/
theorem cleaved_bonds_absent :
    bondedX C2 C3 = false ∧ bondedX C3 OAnhydro = false := by decide

/-- The reduction-installed C3 hydroxymethyl bond is present in X. -/
theorem installed_bond_present : bondedX C3 OHydroxylC3 = true := by decide

/-- Every precursor bond that was not cleaved is retained in X. -/
theorem retained_bonds : ∀ a b : PrecursorAtom,
    precursorBonded a b = true → memBond cleavedBonds (embedK a) (embedK b) = false →
    bondedX (embedK a) (embedK b) = true := by decide

/-- Chemical elements occurring in the carbon/oxygen skeleton. -/
inductive ChemElement : Type where
  | carbon | oxygen
  deriving DecidableEq, Repr, BEq

/-- Ligand data attached to a heavy atom: its element and the number of
implicit hydrogen atoms completing its valence.  After the NaBH₄
reduction all bonds are single, so for carbon `hydrogens = 4 − degree`
and for the oxygen vertices `hydrogens ∈ {0, 1}` (ether vs hydroxyl). -/
structure AtomLabel where
  element : ChemElement
  hydrogens : ℕ
  deriving DecidableEq, Repr

/-- Ligand data of the precursor K (on the precursor carrier; the
product-only C3 hydroxyl case is vacuous by the carrier constraint). -/
def labelK (a : PrecursorAtom) : AtomLabel :=
  match a with
  | ⟨.C1, _⟩ => ⟨.carbon, 1⟩   -- acetal CH
  | ⟨.C2, _⟩ => ⟨.carbon, 1⟩   -- carbinol CH
  | ⟨.C3, _⟩ => ⟨.carbon, 1⟩   -- ether CH
  | ⟨.C4, _⟩ => ⟨.carbon, 1⟩   -- glycosidic CH
  | ⟨.C5, _⟩ => ⟨.carbon, 1⟩   -- ring CH
  | ⟨.C6, _⟩ => ⟨.carbon, 2⟩   -- bridge CH₂
  | ⟨.O5, _⟩ => ⟨.oxygen, 0⟩   -- ring ether
  | ⟨.OAnhydro, _⟩ => ⟨.oxygen, 0⟩  -- bridge ether
  | ⟨.OGly, _⟩ => ⟨.oxygen, 0⟩      -- glycosidic ether
  | ⟨.OHydroxylC2, _⟩ => ⟨.oxygen, 1⟩  -- the one free OH of K
  | ⟨.OHydroxylC3, h⟩ => absurd h (by decide)

/-- Ligand data of **X** (on the full carrier, including the installed
C3 hydroxyl).  The final Ac₂O/Py step replaces the three free hydroxyl
hydrogens per unit by acetyl groups; the acetyl atoms are suppressed here
because they are exocyclic leaves (never on a cycle) and achiral
(methyl/carbonyl carbons), so they can change neither `rs` nor `sc`, and
capping leaves every ligand-distinctness relation below intact. -/
def labelX : UnitAtom → AtomLabel
  | .C1 => ⟨.carbon, 1⟩   -- acetal CH (retained)
  | .C2 => ⟨.carbon, 2⟩   -- reduced: hydroxymethyl CH₂
  | .C3 => ⟨.carbon, 2⟩   -- reduced: hydroxymethyl CH₂
  | .C4 => ⟨.carbon, 1⟩   -- retained CH
  | .C5 => ⟨.carbon, 1⟩   -- retained CH
  | .C6 => ⟨.carbon, 2⟩   -- hydroxymethyl CH₂
  | .O5 => ⟨.oxygen, 0⟩   -- acetal oxygen
  | .OAnhydro => ⟨.oxygen, 1⟩  -- released bridge O, now the C6 hydroxyl
  | .OGly => ⟨.oxygen, 0⟩      -- glycosidic (acetal) oxygen
  | .OHydroxylC2 => ⟨.oxygen, 1⟩  -- C2 hydroxymethyl hydroxyl
  | .OHydroxylC3 => ⟨.oxygen, 1⟩  -- installed C3 hydroxyl

/-- The ligand-data transformation, machine-checked on every precursor
atom: reduction saturates the two cleaved carbons C2 and C3 (CH → CH₂)
and protonates the released bridge oxygen; every other precursor atom
keeps its K label. -/
theorem labelX_eq_labelK_transform : ∀ a : PrecursorAtom, labelX (embedK a) =
    (if a.1 = C2 ∨ a.1 = C3 then ⟨(labelK a).element, 2⟩
     else if a.1 = OAnhydro then ⟨.oxygen, 1⟩
     else labelK a) := by decide

/-- The installed C3 hydroxyl carries the label of a hydroxyl oxygen. -/
theorem labelX_new_hydroxyl : labelX OHydroxylC3 = ⟨.oxygen, 1⟩ := rfl

/-- Tetrahedral configuration data of the precursor K, derived from the
α-D-glucose configurations: every one of the five stereocentres of a
3,6-anhydro-α-D-glucopyranoside unit (C1 the α-anomer; C2; C3, whose
configuration is retained from glucose because the anhydro bridge forms
by attack at C6; C4; C5) carries a configuration label.  The labels are
abstract tetrahedral parities relative to the canonical atom-numbering
ligand order at each centre — stereochemical *reference* data, not
stereocentre markers for X. -/
def configK (a : PrecursorAtom) : Option Bool :=
  match a with
  | ⟨.C1, _⟩ => some false   -- α anomeric configuration
  | ⟨.C2, _⟩ => some false
  | ⟨.C3, _⟩ => some true
  | ⟨.C4, _⟩ => some false
  | ⟨.C5, _⟩ => some true
  | ⟨.OHydroxylC3, h⟩ => absurd h (by decide)
  | _ => none           -- oxygens and the CH₂ carbon C6 carry no label

/-- Stereochemical reference data of **X**, obtained from `configK` by the
reaction transform: the reduction destroys the tetrahedral centres at C2
and C3 (they become CH₂), the acetal carbon C1 is deliberately left
unlabelled — its stereochemical status in X is exactly what must be
derived — and only the C4/C5 branch labels survive, as the retained
stereochemical references of the *meso*-butanetetrol half (opposite
labels, inherited from the glucose configurations at C4 and C5). -/
def configX : UnitAtom → Option Bool
  | .C4 => configK (pk C4)   -- retained reference label
  | .C5 => configK (pk C5)   -- retained reference label
  | _ => none                -- destroyed (C2, C3) or unmarked (C1)

/-- The stereochemical-data transformation, machine-checked on every
precursor atom: only the C4 and C5 labels are retained; C2 and C3 (whose
centres are destroyed) and C1 (deliberately unmarked) carry no label in
X. -/
theorem configX_eq_configK_transform : ∀ a : PrecursorAtom,
    configX (embedK a) = (if a.1 = C4 ∨ a.1 = C5 then configK a else none) := by
  decide

/-- The acetal carbon is unlabelled in X: its stereogenicity is derived,
not marked. -/
theorem configX_C1_unlabelled : configX C1 = none := rfl

/-- The two retained reference labels of a unit differ: the
meso-butanetetrol relationship of the marking scheme. -/
theorem configX_C4_ne_configX_C5 : configX C4 ≠ configX C5 := by decide

/-- Glucopyranoside units of β-cyclodextrin.  Source data (problem text,
page 1): α-, β-, γ-cyclodextrin contain 6, 7 and 8 α-D-glucopyranoside
units respectively, and the T9 scheme starts from β-CD. -/
def betaCDUnits : ℕ := 7

/-- Repeat units of macrocycle X.  The sequence β-CD → K → X touches no
glycosidic bond and removes no heavy atom from the macrocyclic backbone,
so X remains a cyclic heptamer: one repeat unit per β-CD unit. -/
def repeatUnitsX : ℕ := betaCDUnits

instance : NeZero repeatUnitsX := ⟨by decide⟩

/-- The heavy atoms of macrocycle X, indexed by repeat unit and by atom
within the unit. -/
abbrev MacrocycleAtom := Fin repeatUnitsX × UnitAtom

/-- Adjacency in the molecular graph of X: intra-unit bonds are the
transformed bonds `bondedX`; the only inter-unit bonds are the
α-1,4-glycosidic linkages, the glycosidic oxygen of unit `j` bonding to
C4 of unit `j + 1` (indices modulo `repeatUnitsX`, since the macrocycle
is closed). -/
def macrocycleAdj (x y : MacrocycleAtom) : Prop :=
  (x.1 = y.1 ∧ bondedX x.2 y.2 = true) ∨
  (x.2 = OGly ∧ y.2 = C4 ∧ y.1 = x.1 + 1) ∨
  (y.2 = OGly ∧ x.2 = C4 ∧ x.1 = y.1 + 1)

instance decidableMacrocycleAdj : DecidableRel macrocycleAdj := fun x y =>
  inferInstanceAs (Decidable ((x.1 = y.1 ∧ bondedX x.2 y.2 = true) ∨
    (x.2 = OGly ∧ y.2 = C4 ∧ y.1 = x.1 + 1) ∨
    (y.2 = OGly ∧ x.2 = C4 ∧ x.1 = y.1 + 1)))

/-- The molecular graph of macrocycle X on its heavy atoms. -/
def macrocycleGraph : SimpleGraph MacrocycleAtom where
  Adj := macrocycleAdj
  symm := ⟨by
    rintro x y (⟨h1, h2⟩ | ⟨hxO, hyC, hk⟩ | ⟨hyO, hxC, hj⟩)
    · exact Or.inl ⟨h1.symm, by rw [bondedX_symm]; exact h2⟩
    · exact Or.inr (Or.inr ⟨hxO, hyC, hk⟩)
    · exact Or.inr (Or.inl ⟨hyO, hxC, hj⟩)⟩
  loopless := ⟨by
    rintro x (⟨h1, h2⟩ | ⟨hxO, hxC, _⟩ | ⟨hxO, hxC, _⟩)
    · rw [bondedX_irrefl] at h2; exact Bool.false_ne_true h2
    · exact UnitAtom.noConfusion (hxO.symm.trans hxC)
    · exact UnitAtom.noConfusion (hxO.symm.trans hxC)⟩

instance : DecidableRel macrocycleGraph.Adj := decidableMacrocycleAdj

/-- The ligand label of an atom of X (uniform across the identical
units). -/
def macrocycleLabel : MacrocycleAtom → AtomLabel := fun a => labelX a.2

/-- The stereochemical reference label of an atom of X (uniform across
the identical units). -/
def configLabel : MacrocycleAtom → Option Bool := fun a => configX a.2

/-- A constitutional automorphism of X: a permutation of its heavy atoms
preserving adjacency and ligand labels (element and hydrogen count), and
ignoring stereochemical reference labels.  This is the automorphism group
of the *labelled molecular graph* in the usual chemical sense. -/
structure ConstitutionalAutomorphism where
  toEquiv : MacrocycleAtom ≃ MacrocycleAtom
  map_adj : ∀ a b, macrocycleGraph.Adj a b ↔ macrocycleGraph.Adj (toEquiv a) (toEquiv b)
  map_label : ∀ a, macrocycleLabel (toEquiv a) = macrocycleLabel a

/-- A stereochemical automorphism of X: a constitutional automorphism that
additionally preserves every stereochemical reference label.  Ligands
interchanged only by automorphisms that swap opposite reference labels
(the two ring directions at the acetal carbon, which exchange the
oppositely labelled C4/C5 branches) are *enantiomorphic*: distinct for
stereogenicity, identical constitutionally — the source of
pseudochirality. -/
structure StereochemicalAutomorphism extends ConstitutionalAutomorphism where
  map_config : ∀ a, configLabel (toEquiv a) = configLabel a

/-- The identity automorphism (constitutional): the equivalence notions
below are reflexive, hence not vacuous. -/
def ConstitutionalAutomorphism.refl : ConstitutionalAutomorphism where
  toEquiv := Equiv.refl _
  map_adj := fun _ _ => Iff.rfl
  map_label := fun _ => rfl

/-- The identity automorphism (stereochemical). -/
def StereochemicalAutomorphism.refl : StereochemicalAutomorphism where
  toEquiv := Equiv.refl _
  map_adj := fun _ _ => Iff.rfl
  map_label := fun _ => rfl
  map_config := fun _ => rfl

/-- Two heavy-atom ligands attached to a centre `c` are *stereochemically
equivalent* iff some stereochemical automorphism fixes `c` and maps one
ligand to the other.  (Implicit hydrogen ligands are handled separately:
two hydrogens are always equivalent, a hydrogen never equivalent to a
heavy-atom ligand.) -/
def LigandEquivalent (c n₁ n₂ : MacrocycleAtom) : Prop :=
  ∃ σ : StereochemicalAutomorphism, σ.toEquiv c = c ∧ σ.toEquiv n₁ = n₂

/-- Constitutional (stereochemistry-blind) ligand equivalence at `c`. -/
def LigandEquivalentConstitutional (c n₁ n₂ : MacrocycleAtom) : Prop :=
  ∃ σ : ConstitutionalAutomorphism, σ.toEquiv c = c ∧ σ.toEquiv n₁ = n₂

/-- Ligand equivalence is reflexive (via the identity automorphism). -/
theorem ligandEquivalent_refl (c n : MacrocycleAtom) : LigandEquivalent c n n :=
  ⟨.refl, rfl, rfl⟩

/-- Constitutional ligand equivalence is reflexive. -/
theorem ligandEquivalentConstitutional_refl (c n : MacrocycleAtom) :
    LigandEquivalentConstitutional c n n :=
  ⟨.refl, rfl, rfl⟩

/-- **General four-distinct-ligands predicate.**  An atom of X is a
stereocentre iff it is a carbon carrying four pairwise distinct ligands:
at most one implicit hydrogen (two or more H ligands would coincide), at
least three heavy-atom neighbours (valence 4 minus the hydrogens), and no
two distinct heavy-atom ligands interchangeable by a stereochemical
automorphism fixing the centre.  Nothing about specific atoms is
hard-wired; in particular the acetal carbon C1 carries no label and is
tested like any other atom. -/
def IsStereocentre (c : MacrocycleAtom) : Prop :=
  (macrocycleLabel c).element = .carbon ∧
  (macrocycleLabel c).hydrogens ≤ 1 ∧
  3 ≤ macrocycleGraph.degree c ∧
  ∀ n₁ n₂ : MacrocycleAtom, macrocycleGraph.Adj c n₁ → macrocycleGraph.Adj c n₂ →
    n₁ ≠ n₂ → ¬ LigandEquivalent c n₁ n₂

/-- A pseudochiral (pseudoasymmetric) centre: a stereocentre two of whose
ligands are constitutionally equivalent — interchangeable once the
stereochemical reference labels are ignored — so that it is stereogenic
only through the stereochemistry of remote centres.  The marking scheme:
"one of which (the acetal) is pseudochiral". -/
def IsPseudochiralCentre (c : MacrocycleAtom) : Prop :=
  IsStereocentre c ∧
    ∃ n₁ n₂ : MacrocycleAtom, macrocycleGraph.Adj c n₁ ∧ macrocycleGraph.Adj c n₂ ∧
      n₁ ≠ n₂ ∧ LigandEquivalentConstitutional c n₁ n₂

/-- A true stereocentre (a chirality centre): stereogenic and not
pseudochiral. -/
def IsTrueStereocentre (c : MacrocycleAtom) : Prop :=
  IsStereocentre c ∧ ¬ IsPseudochiralCentre c

/-- **Ring inventory from graph connectivity.**  An atom of X lies on the
macrocyclic ring iff it lies on a cycle of the molecular graph.  After
the C2–C3 cleavage the only cycle of `macrocycleGraph` is the 35-membered
macrocycle itself (every other bond lies on a pendant tree: the
hydroxymethyl substituents and hydroxyls), so this predicate picks out
exactly the ring atoms, per unit {C1, O5, C5, C4, OGly}. -/
def IsRingAtom (a : MacrocycleAtom) : Prop :=
  ∃ p : macrocycleGraph.Walk a a, p.IsCycle

/-- The atoms of one repeat unit `j` that lie on the macrocyclic ring. -/
noncomputable def ringAtomsOfUnit (j : Fin repeatUnitsX) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : MacrocycleAtom => a.1 = j ∧ IsRingAtom a)).card

/-- The stereocentres (including pseudochiral centres, per the marking
scheme's full-credit convention) of one repeat unit `j`. -/
noncomputable def stereocentresOfUnit (j : Fin repeatUnitsX) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : MacrocycleAtom => a.1 = j ∧ IsStereocentre a)).card

/-- The pseudochiral centres of one repeat unit `j`. -/
noncomputable def pseudochiralCentresOfUnit (j : Fin repeatUnitsX) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : MacrocycleAtom => a.1 = j ∧
    IsPseudochiralCentre a)).card

/-- The ring size `rs` of macrocycle X: the total number of atoms forming
the macrocyclic ring. -/
noncomputable def ringSizeX : ℕ := by
  classical
  exact (Finset.univ.filter IsRingAtom).card

/-- The number of stereocentres `sc` in macrocycle X. -/
noncomputable def stereocentresX : ℕ := by
  classical
  exact (Finset.univ.filter IsStereocentre).card

/-- Degree check: the acetal carbon C1 has three heavy-atom neighbours in
X (C2, O5, OGly). -/
theorem degree_C1_eq_three :
    ∀ j : Fin repeatUnitsX, macrocycleGraph.degree (j, C1) = 3 := by decide

/-- Degree check: C4 has three heavy-atom neighbours in X (C3, C5 and the
previous unit's glycosidic oxygen). -/
theorem degree_C4_eq_three :
    ∀ j : Fin repeatUnitsX, macrocycleGraph.degree (j, C4) = 3 := by decide

/-- Degree check: C5 has three heavy-atom neighbours in X (C4, C6, O5). -/
theorem degree_C5_eq_three :
    ∀ j : Fin repeatUnitsX, macrocycleGraph.degree (j, C5) = 3 := by decide

/-- Degree check: the cleaved/reduced carbons C2 and C3 and the bridge
methylene C6 each have two heavy-atom neighbours in X. -/
theorem degree_methylenes_eq_two : ∀ j : Fin repeatUnitsX,
    macrocycleGraph.degree (j, C2) = 2 ∧ macrocycleGraph.degree (j, C3) = 2 ∧
    macrocycleGraph.degree (j, C6) = 2 := by decide

/-- The cleavage destroys the former C2 and C3 stereocentres: after
reduction each is a hydroxymethyl carbon with two hydrogen ligands, which
coincide, so the four-distinct-ligands predicate fails immediately.
(Provable from `labelX` alone.) -/
theorem cleavage_destroys_C2_C3_stereocentres (j : Fin repeatUnitsX) :
    ¬ IsStereocentre (j, C2) ∧ ¬ IsStereocentre (j, C3) := by
  constructor
  · intro h
    have h2 := h.2.1
    simp [macrocycleLabel, labelX] at h2
  · intro h
    have h2 := h.2.1
    simp [macrocycleLabel, labelX] at h2

/-- The C6 methylene is not a stereocentre either (two hydrogen ligands;
it already was a methylene in K). -/
theorem C6_not_stereocentre (j : Fin repeatUnitsX) : ¬ IsStereocentre (j, C6) := by
  intro h
  have h2 := h.2.1
  simp [macrocycleLabel, labelX] at h2

/-- The unit bond list of **X** as a literal: the graph transformation
(filter out the cleaved bonds, append the installed one) computes to exactly
these ten bonds.  Used to make kernel `decide` checks on adjacency cheap. -/
theorem bondsX_eq_literal : bondsX =
    [(C1, C2), (C3, C4), (C4, C5), (C5, O5), (O5, C1), (OAnhydro, C6),
     (C6, C5), (C1, OGly), (C2, OHydroxylC2), (C3, OHydroxylC3)] := by decide

/-- Neighbor inventory at the acetal carbon C1: the hydroxymethyl carbon C2
and the two ring oxygens O5 (pyranose) and OGly (glycosidic). -/
theorem neighbors_C1 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, C1) z ↔ z = (j, C2) ∨ z = (j, O5) ∨ z = (j, OGly) := by
  decide

/-- Neighbor inventory at the pyranose oxygen O5: C1 and C5 of its unit. -/
theorem neighbors_O5 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, O5) z ↔ z = (j, C5) ∨ z = (j, C1) := by
  decide

/-- Neighbor inventory at the glycosidic oxygen OGly: C1 of its unit and C4
of the next unit. -/
theorem neighbors_OGly : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, OGly) z ↔ z = (j, C1) ∨ z = (j + 1, C4) := by
  decide

/-- Neighbor inventory at C4: the pendant hydroxymethyl C3, the ring carbon
C5, and the previous unit's glycosidic oxygen. -/
theorem neighbors_C4 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, C4) z ↔
      z = (j, C3) ∨ z = (j, C5) ∨ z = (j - 1, OGly) := by
  decide

/-- Neighbor inventory at C5: the ring carbon C4, the pyranose oxygen O5 and
the pendant hydroxymethyl C6. -/
theorem neighbors_C5 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, C5) z ↔ z = (j, C4) ∨ z = (j, O5) ∨ z = (j, C6) := by
  decide

/-- Neighbor inventory at the reduced C2 hydroxymethyl carbon: the acetal
carbon C1 and its hydroxyl oxygen. -/
theorem neighbors_C2 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, C2) z ↔ z = (j, C1) ∨ z = (j, OHydroxylC2) := by
  decide

/-- Neighbor inventory at the reduced C3 hydroxymethyl carbon: C4 and its
installed hydroxyl oxygen. -/
theorem neighbors_C3 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, C3) z ↔ z = (j, C4) ∨ z = (j, OHydroxylC3) := by
  decide

/-- Neighbor inventory at C6: C5 and the released bridge/hydroxyl oxygen. -/
theorem neighbors_C6 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, C6) z ↔ z = (j, C5) ∨ z = (j, OAnhydro) := by
  decide

/-- The C2 hydroxyl oxygen is a leaf: its only neighbor is C2. -/
theorem neighbors_OHydroxylC2 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, OHydroxylC2) z ↔ z = (j, C2) := by
  decide

/-- The installed C3 hydroxyl oxygen is a leaf: its only neighbor is C3. -/
theorem neighbors_OHydroxylC3 : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, OHydroxylC3) z ↔ z = (j, C3) := by
  decide

/-- The released bridge oxygen (now the C6 hydroxyl) is a leaf: its only
neighbor is C6. -/
theorem neighbors_OAnhydro : ∀ (j : Fin repeatUnitsX) (z : MacrocycleAtom),
    macrocycleGraph.Adj (j, OAnhydro) z ↔ z = (j, C6) := by
  decide

/-- The configuration-blind **reflection** of X about the acetal carbon C1 of
unit `i`: the graph automorphism exchanging the two ring directions at that
acetal carbon.  On the ring it swaps O5/C5/C4/OGly of each unit offset `k`
from `i` with OGly/C4/C5/O5 at offset `1 - k` from `i` (unit `i`'s C1 and the
C4–C5 bond opposite to it are fixed); pendant hydroxymethyl/hydroxyl groups
follow their attachment atoms.  It fixes `(i, C1)` and interchanges its two
ring-oxygen ligands `(i, O5)` and `(i, OGly)` — the witness of the acetal
carbon's pseudochirality. -/
def reflectAbout (i : Fin repeatUnitsX) : MacrocycleAtom → MacrocycleAtom
  | (j, C1) => (i + (i - j), C1)
  | (j, C2) => (i + (i - j), C2)
  | (j, OHydroxylC2) => (i + (i - j), OHydroxylC2)
  | (j, O5) => (i + (i - j), OGly)
  | (j, OGly) => (i + (i - j), O5)
  | (j, C4) => (i + (i - j) + 1, C5)
  | (j, C5) => (i + (i - j) + 1, C4)
  | (j, C3) => (i + (i - j) + 1, C6)
  | (j, C6) => (i + (i - j) + 1, C3)
  | (j, OAnhydro) => (i + (i - j) + 1, OHydroxylC3)
  | (j, OHydroxylC3) => (i + (i - j) + 1, OAnhydro)

/-- The reflection is an involution (checked on all `7 × 77` inputs). -/
theorem reflectAbout_involutive :
    ∀ i : Fin repeatUnitsX, Function.Involutive (reflectAbout i) := by
  unfold Function.Involutive
  decide

/-- The reflection as an equivalence (it is its own inverse). -/
def reflectionEquiv (i : Fin repeatUnitsX) : MacrocycleAtom ≃ MacrocycleAtom where
  toFun := reflectAbout i
  invFun := reflectAbout i
  left_inv := reflectAbout_involutive i
  right_inv := reflectAbout_involutive i

/-- The reflection fixes the acetal carbon of the axis unit. -/
theorem reflectAbout_self_C1 :
    ∀ j : Fin repeatUnitsX, reflectAbout j (j, C1) = (j, C1) := by decide

/-- The reflection swaps the two ring-oxygen ligands of the axis unit's
acetal carbon. -/
theorem reflectAbout_self_O5 :
    ∀ j : Fin repeatUnitsX, reflectAbout j (j, O5) = (j, OGly) := by decide

/-- The reflection preserves ligand labels (element and hydrogen count). -/
theorem reflectAbout_map_label : ∀ (i : Fin repeatUnitsX) (a : MacrocycleAtom),
    macrocycleLabel (reflectAbout i a) = macrocycleLabel a := by decide

/-- Index identity behind the reflection of the inter-unit glycosidic bond:
the image of `(j + 1, C4)` lands in the same unit as the image of
`(j, OGly)`.  Checked on all `7 × 7` index pairs. -/
theorem reflect_index_aux :
    ∀ i j : Fin repeatUnitsX, i + (i - (j + 1)) + 1 = i + (i - j) := by decide

/-- The reflection maps bonds to bonds (forward direction of adjacency
preservation).  Proved by case analysis on the three adjacency clauses; the
intra-unit clause splits into the `10 × 10` atom pairs, each discharged by
the literal bond list. -/
theorem reflectAbout_map_adj_forward : ∀ (i : Fin repeatUnitsX) (a b : MacrocycleAtom),
    macrocycleAdj a b → macrocycleAdj (reflectAbout i a) (reflectAbout i b) := by
  intro i a b h
  obtain ⟨j, x⟩ := a
  obtain ⟨k, y⟩ := b
  rcases h with ⟨h1, h2⟩ | ⟨hx, hy, hk⟩ | ⟨hy, hx, hk⟩
  · change j = k at h1
    change bondedX x y = true at h2
    subst h1
    cases x <;> cases y <;>
      first
        | exact absurd h2 (by decide)
        | exact Or.inl ⟨rfl, by decide +revert⟩
        | exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
        | exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
  · change x = OGly at hx
    change y = C4 at hy
    change k = j + 1 at hk
    subst hx; subst hy; subst hk
    exact Or.inl ⟨(reflect_index_aux i j).symm, by decide +revert⟩
  · change y = OGly at hy
    change x = C4 at hx
    change j = k + 1 at hk
    subst hx; subst hy; subst hk
    exact Or.inl ⟨reflect_index_aux i k, by decide +revert⟩

/-- The reflection preserves adjacency: forward by
`reflectAbout_map_adj_forward`, converse by applying the forward direction
twice (the reflection is an involution). -/
theorem reflectAbout_map_adj : ∀ (i : Fin repeatUnitsX) (a b : MacrocycleAtom),
    macrocycleAdj a b ↔ macrocycleAdj (reflectAbout i a) (reflectAbout i b) :=
  fun i a b => ⟨reflectAbout_map_adj_forward i a b, fun h => by
    have h' := reflectAbout_map_adj_forward i (reflectAbout i a) (reflectAbout i b) h
    rwa [reflectAbout_involutive i a, reflectAbout_involutive i b] at h'⟩

/-- The reflection about unit `i`'s acetal carbon, packaged as a
constitutional automorphism of X.  It is *not* a stereochemical
automorphism: it swaps the oppositely labelled C4/C5 branches. -/
def reflectionAutomorphism (i : Fin repeatUnitsX) : ConstitutionalAutomorphism where
  toEquiv := reflectionEquiv i
  map_adj := reflectAbout_map_adj i
  map_label := reflectAbout_map_label i

/-- Ligands with different labels can never be interchanged by a
stereochemical automorphism: automorphisms preserve labels, so mapping one
ligand onto the other would equate the labels. -/
theorem not_ligandEquivalent_of_label_ne {c n₁ n₂ : MacrocycleAtom}
    (h : macrocycleLabel n₁ ≠ macrocycleLabel n₂) : ¬ LigandEquivalent c n₁ n₂ := by
  rintro ⟨σ, -, hσ⟩
  have hlab := σ.map_label n₁
  rw [hσ] at hlab
  exact h hlab.symm

/-- The constitutional analogue of `not_ligandEquivalent_of_label_ne`. -/
theorem not_ligandEquivalentConstitutional_of_label_ne {c n₁ n₂ : MacrocycleAtom}
    (h : macrocycleLabel n₁ ≠ macrocycleLabel n₂) :
    ¬ LigandEquivalentConstitutional c n₁ n₂ := by
  rintro ⟨σ, -, hσ⟩
  have hlab := σ.map_label n₁
  rw [hσ] at hlab
  exact h hlab.symm

/-- **The stereochemical obstruction at the acetal carbon.**  No
stereochemical automorphism fixing `(j, C1)` can map its pyranose-oxygen
ligand `(j, O5)` onto its glycosidic-oxygen ligand `(j, OGly)`: such an
automorphism would have to send C5 (the other neighbor of O5) to C4 of the
next unit (the other neighbor of OGly), but those carry the opposite
retained reference labels (`configX_C4_ne_configX_C5`). -/
theorem not_ligandEquivalent_C1_O5_OGly (j : Fin repeatUnitsX) :
    ¬ LigandEquivalent (j, C1) (j, O5) (j, OGly) := by
  rintro ⟨σ, hc, hσ⟩
  have hadj : macrocycleGraph.Adj (j, O5) (j, C5) :=
    (neighbors_O5 j (j, C5)).mpr (Or.inl rfl)
  have him := (σ.map_adj _ _).mp hadj
  rw [hσ] at him
  rcases (neighbors_OGly j _).mp him with h1 | h1
  · -- σ (j, C5) = (j, C1) = σ (j, C1): contradicts injectivity
    have h := σ.toEquiv.injective (h1.trans hc.symm)
    exact UnitAtom.noConfusion (Prod.mk.inj h).2
  · -- σ (j, C5) = (j+1, C4): contradicts the retained reference labels
    have hconf := σ.map_config (j, C5)
    rw [h1] at hconf
    exact configX_C4_ne_configX_C5 hconf

/-- The mirror image of `not_ligandEquivalent_C1_O5_OGly`: no stereochemical
automorphism fixing `(j, C1)` maps the glycosidic oxygen onto the pyranose
oxygen (this time C4 of the next unit would have to land on C5). -/
theorem not_ligandEquivalent_C1_OGly_O5 (j : Fin repeatUnitsX) :
    ¬ LigandEquivalent (j, C1) (j, OGly) (j, O5) := by
  rintro ⟨σ, hc, hσ⟩
  have hadj : macrocycleGraph.Adj (j, OGly) (j + 1, C4) :=
    (neighbors_OGly j (j + 1, C4)).mpr (Or.inr rfl)
  have him := (σ.map_adj _ _).mp hadj
  rw [hσ] at him
  rcases (neighbors_O5 j _).mp him with h1 | h1
  · -- σ (j+1, C4) = (j, C5): contradicts the retained reference labels
    have hconf := σ.map_config (j + 1, C4)
    rw [h1] at hconf
    exact configX_C4_ne_configX_C5 hconf.symm
  · -- σ (j+1, C4) = (j, C1) = σ (j, C1): contradicts injectivity
    have h := σ.toEquiv.injective (h1.trans hc.symm)
    exact UnitAtom.noConfusion (Prod.mk.inj h).2

/-- The acetal carbon of each unit is a stereocentre: carbon with one
hydrogen and three heavy-atom ligands, and no two ligands are
stereochemically equivalent — C2 differs from both oxygens by label, and
the two ring oxygens differ by the configuration obstruction. -/
theorem C1_isStereocentre (j : Fin repeatUnitsX) : IsStereocentre (j, C1) := by
  refine ⟨by simp [macrocycleLabel, labelX], by simp [macrocycleLabel, labelX],
    (degree_C1_eq_three j).ge, ?_⟩
  intro n₁ n₂ h₁ h₂ hne
  have hn₁ := (neighbors_C1 j n₁).mp h₁
  have hn₂ := (neighbors_C1 j n₂).mp h₂
  rcases hn₁ with rfl | rfl | rfl <;> rcases hn₂ with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact not_ligandEquivalent_of_label_ne (by simp [macrocycleLabel, labelX])
  · exact not_ligandEquivalent_of_label_ne (by simp [macrocycleLabel, labelX])
  · exact not_ligandEquivalent_of_label_ne (by simp [macrocycleLabel, labelX])
  · exact absurd rfl hne
  · exact not_ligandEquivalent_C1_O5_OGly j
  · exact not_ligandEquivalent_of_label_ne (by simp [macrocycleLabel, labelX])
  · exact not_ligandEquivalent_C1_OGly_O5 j
  · exact absurd rfl hne

/-- C4 of each unit is a stereocentre: its three ligands (the C3
hydroxymethyl, the ring carbon C5, the previous unit's glycosidic oxygen)
have pairwise distinct labels, so no automorphism can interchange any two. -/
theorem C4_isStereocentre (j : Fin repeatUnitsX) : IsStereocentre (j, C4) := by
  refine ⟨by simp [macrocycleLabel, labelX], by simp [macrocycleLabel, labelX],
    (degree_C4_eq_three j).ge, ?_⟩
  intro n₁ n₂ h₁ h₂ hne
  have hn₁ := (neighbors_C4 j n₁).mp h₁
  have hn₂ := (neighbors_C4 j n₂).mp h₂
  rcases hn₁ with rfl | rfl | rfl <;> rcases hn₂ with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | exact not_ligandEquivalent_of_label_ne (by simp [macrocycleLabel, labelX])

/-- C4 is not pseudochiral: pseudochirality would require two ligands
interchangeable by a constitutional automorphism, impossible across the
pairwise distinct ligand labels. -/
theorem C4_not_pseudochiral (j : Fin repeatUnitsX) :
    ¬ IsPseudochiralCentre (j, C4) := by
  rintro ⟨-, n₁, n₂, h₁, h₂, hne, hleq⟩
  have hn₁ := (neighbors_C4 j n₁).mp h₁
  have hn₂ := (neighbors_C4 j n₂).mp h₂
  rcases hn₁ with rfl | rfl | rfl <;> rcases hn₂ with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | exact not_ligandEquivalentConstitutional_of_label_ne
          (by simp [macrocycleLabel, labelX]) hleq

/-- C5 of each unit is a stereocentre: its three ligands (the ring carbon
C4, the pyranose oxygen O5, the C6 hydroxymethyl) have pairwise distinct
labels. -/
theorem C5_isStereocentre (j : Fin repeatUnitsX) : IsStereocentre (j, C5) := by
  refine ⟨by simp [macrocycleLabel, labelX], by simp [macrocycleLabel, labelX],
    (degree_C5_eq_three j).ge, ?_⟩
  intro n₁ n₂ h₁ h₂ hne
  have hn₁ := (neighbors_C5 j n₁).mp h₁
  have hn₂ := (neighbors_C5 j n₂).mp h₂
  rcases hn₁ with rfl | rfl | rfl <;> rcases hn₂ with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | exact not_ligandEquivalent_of_label_ne (by simp [macrocycleLabel, labelX])

/-- C5 is not pseudochiral, by the same label-distinctness argument as C4. -/
theorem C5_not_pseudochiral (j : Fin repeatUnitsX) :
    ¬ IsPseudochiralCentre (j, C5) := by
  rintro ⟨-, n₁, n₂, h₁, h₂, hne, hleq⟩
  have hn₁ := (neighbors_C5 j n₁).mp h₁
  have hn₂ := (neighbors_C5 j n₂).mp h₂
  rcases hn₁ with rfl | rfl | rfl <;> rcases hn₂ with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | exact not_ligandEquivalentConstitutional_of_label_ne
          (by simp [macrocycleLabel, labelX]) hleq

/-- The only possible stereocentre atoms of X: a stereocentre must be a
carbon carrying at most one hydrogen, which rules out every atom except
C1, C4 and C5. -/
theorem stereocentre_atom_types {a : MacrocycleAtom} (h : IsStereocentre a) :
    a.2 = C1 ∨ a.2 = C4 ∨ a.2 = C5 := by
  obtain ⟨i, b⟩ := a
  obtain ⟨hel, hh, -, -⟩ := h
  cases b
  · exact Or.inl rfl
  · exact absurd hh (by simp [macrocycleLabel, labelX])
  · exact absurd hh (by simp [macrocycleLabel, labelX])
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact absurd hh (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])

/-- The unique cycle of the molecular graph of X, as an explicit
35-edge closed walk: it starts at `(0, C4)` and runs through
`C4–C5–O5–C1–OGly` of every unit in turn, closing through the
glycosidic bond from unit 6 back to unit 0.  Every ring atom of X
occurs in its support. -/
def ringCycle : macrocycleGraph.Walk (0, C4) (0, C4) :=
  .cons (by decide : macrocycleGraph.Adj (0, C4) (0, C5)) <|
  .cons (by decide : macrocycleGraph.Adj (0, C5) (0, O5)) <|
  .cons (by decide : macrocycleGraph.Adj (0, O5) (0, C1)) <|
  .cons (by decide : macrocycleGraph.Adj (0, C1) (0, OGly)) <|
  .cons (by decide : macrocycleGraph.Adj (0, OGly) (1, C4)) <|
  .cons (by decide : macrocycleGraph.Adj (1, C4) (1, C5)) <|
  .cons (by decide : macrocycleGraph.Adj (1, C5) (1, O5)) <|
  .cons (by decide : macrocycleGraph.Adj (1, O5) (1, C1)) <|
  .cons (by decide : macrocycleGraph.Adj (1, C1) (1, OGly)) <|
  .cons (by decide : macrocycleGraph.Adj (1, OGly) (2, C4)) <|
  .cons (by decide : macrocycleGraph.Adj (2, C4) (2, C5)) <|
  .cons (by decide : macrocycleGraph.Adj (2, C5) (2, O5)) <|
  .cons (by decide : macrocycleGraph.Adj (2, O5) (2, C1)) <|
  .cons (by decide : macrocycleGraph.Adj (2, C1) (2, OGly)) <|
  .cons (by decide : macrocycleGraph.Adj (2, OGly) (3, C4)) <|
  .cons (by decide : macrocycleGraph.Adj (3, C4) (3, C5)) <|
  .cons (by decide : macrocycleGraph.Adj (3, C5) (3, O5)) <|
  .cons (by decide : macrocycleGraph.Adj (3, O5) (3, C1)) <|
  .cons (by decide : macrocycleGraph.Adj (3, C1) (3, OGly)) <|
  .cons (by decide : macrocycleGraph.Adj (3, OGly) (4, C4)) <|
  .cons (by decide : macrocycleGraph.Adj (4, C4) (4, C5)) <|
  .cons (by decide : macrocycleGraph.Adj (4, C5) (4, O5)) <|
  .cons (by decide : macrocycleGraph.Adj (4, O5) (4, C1)) <|
  .cons (by decide : macrocycleGraph.Adj (4, C1) (4, OGly)) <|
  .cons (by decide : macrocycleGraph.Adj (4, OGly) (5, C4)) <|
  .cons (by decide : macrocycleGraph.Adj (5, C4) (5, C5)) <|
  .cons (by decide : macrocycleGraph.Adj (5, C5) (5, O5)) <|
  .cons (by decide : macrocycleGraph.Adj (5, O5) (5, C1)) <|
  .cons (by decide : macrocycleGraph.Adj (5, C1) (5, OGly)) <|
  .cons (by decide : macrocycleGraph.Adj (5, OGly) (6, C4)) <|
  .cons (by decide : macrocycleGraph.Adj (6, C4) (6, C5)) <|
  .cons (by decide : macrocycleGraph.Adj (6, C5) (6, O5)) <|
  .cons (by decide : macrocycleGraph.Adj (6, O5) (6, C1)) <|
  .cons (by decide : macrocycleGraph.Adj (6, C1) (6, OGly)) <|
  .cons (by decide : macrocycleGraph.Adj (6, OGly) (0, C4)) <|
  .nil
/-- The explicit 35-edge walk is a cycle: its edges are distinct (a trail),
it is nonempty, and the tail of its support has no repeated vertex — all
kernel checks on the concrete walk. -/
theorem ringCycle_isCycle : ringCycle.IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · decide
  · intro h
    have hlen : ringCycle.length = 35 := by decide
    rw [h] at hlen
    exact absurd hlen (by decide)
  · decide

/-- Every vertex of the explicit cycle is a ring atom (rotate the cycle to
start at the vertex). -/
theorem isRingAtom_of_mem_ringCycle_support {a : MacrocycleAtom}
    (h : a ∈ ringCycle.support) : IsRingAtom a :=
  ⟨ringCycle.rotate a h, (SimpleGraph.Walk.isCycle_rotate h).mpr ringCycle_isCycle⟩

/-- The positions of unit `j`'s five ring atoms along the explicit cycle:
unit `j` occupies positions `5j` (C4) through `5j + 4` (OGly). -/
theorem ringCycle_getVert_ring_atoms : ∀ j : Fin repeatUnitsX,
    ringCycle.getVert (5 * j.val + 3) = (j, C1) ∧
      ringCycle.getVert (5 * j.val + 2) = (j, O5) ∧
        ringCycle.getVert (5 * j.val + 1) = (j, C5) ∧
          ringCycle.getVert (5 * j.val) = (j, C4) ∧
            ringCycle.getVert (5 * j.val + 4) = (j, OGly) := by
  decide

/-- The five ring atoms of each unit — C1, O5, C5, C4 and the glycosidic
oxygen — all lie on the macrocyclic ring. -/
theorem ringAtoms_mem (j : Fin repeatUnitsX) :
    IsRingAtom (j, C1) ∧ IsRingAtom (j, O5) ∧ IsRingAtom (j, C5) ∧
      IsRingAtom (j, C4) ∧ IsRingAtom (j, OGly) :=
  have h := ringCycle_getVert_ring_atoms j
  ⟨isRingAtom_of_mem_ringCycle_support (h.1 ▸ SimpleGraph.Walk.getVert_mem_support _ _),
   isRingAtom_of_mem_ringCycle_support (h.2.1 ▸ SimpleGraph.Walk.getVert_mem_support _ _),
   isRingAtom_of_mem_ringCycle_support (h.2.2.1 ▸ SimpleGraph.Walk.getVert_mem_support _ _),
   isRingAtom_of_mem_ringCycle_support (h.2.2.2.1 ▸ SimpleGraph.Walk.getVert_mem_support _ _),
   isRingAtom_of_mem_ringCycle_support (h.2.2.2.2 ▸ SimpleGraph.Walk.getVert_mem_support _ _)⟩

/-- A vertex with only one neighbor lies on no cycle: a cycle through it
would need two distinct neighbors (the second and the penultimate vertex of
the walk). -/
theorem not_ringAtom_of_unique_neighbor (a m : MacrocycleAtom)
    (h : ∀ z, macrocycleGraph.Adj a z → z = m) : ¬ IsRingAtom a := by
  rintro ⟨p, hp⟩
  have hnil : ¬ p.Nil := fun hN => hp.ne_nil (SimpleGraph.Walk.eq_nil_iff_nil.mpr hN)
  have h1 := h _ (SimpleGraph.Walk.adj_snd hnil)
  have h2 := h _ (SimpleGraph.Walk.adj_penultimate hnil).symm
  exact hp.snd_ne_penultimate (h1.trans h2.symm)

/-- A vertex whose only neighbors are `b` and the cycle-free vertex `m`
lies on no cycle either: a cycle through it would have to pass through `m`
(second or penultimate vertex), and rotating would give a cycle at `m`. -/
theorem not_ringAtom_of_neighbor_not_ring (a b m : MacrocycleAtom)
    (h : ∀ z, macrocycleGraph.Adj a z → z = b ∨ z = m)
    (hm : ¬ IsRingAtom m) : ¬ IsRingAtom a := by
  rintro ⟨p, hp⟩
  have hnil : ¬ p.Nil := fun hN => hp.ne_nil (SimpleGraph.Walk.eq_nil_iff_nil.mpr hN)
  have hsnd := h _ (SimpleGraph.Walk.adj_snd hnil)
  have hpen := h _ (SimpleGraph.Walk.adj_penultimate hnil).symm
  have hne := hp.snd_ne_penultimate
  have hmem : m ∈ p.support := by
    rcases hsnd with h1 | h1 <;> rcases hpen with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [← h2]; exact List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hnil)
    · rw [← h1]; exact List.mem_of_mem_tail (p.snd_mem_tail_support hnil)
    · exact absurd (h1.trans h2.symm) hne
  exact hm ⟨p.rotate m hmem, (SimpleGraph.Walk.isCycle_rotate hmem).mpr hp⟩

/-- The C2 hydroxyl oxygen is a leaf, hence on no cycle. -/
theorem not_ringAtom_OHydroxylC2 (j : Fin repeatUnitsX) :
    ¬ IsRingAtom (j, OHydroxylC2) :=
  not_ringAtom_of_unique_neighbor _ _ fun z hz => (neighbors_OHydroxylC2 j z).mp hz

/-- The installed C3 hydroxyl oxygen is a leaf, hence on no cycle. -/
theorem not_ringAtom_OHydroxylC3 (j : Fin repeatUnitsX) :
    ¬ IsRingAtom (j, OHydroxylC3) :=
  not_ringAtom_of_unique_neighbor _ _ fun z hz => (neighbors_OHydroxylC3 j z).mp hz

/-- The released bridge oxygen (C6 hydroxyl) is a leaf, hence on no cycle. -/
theorem not_ringAtom_OAnhydro (j : Fin repeatUnitsX) :
    ¬ IsRingAtom (j, OAnhydro) :=
  not_ringAtom_of_unique_neighbor _ _ fun z hz => (neighbors_OAnhydro j z).mp hz

/-- The reduced C2 hydroxymethyl carbon is pendant (its only neighbors are
the acetal carbon and the leaf hydroxyl), hence on no cycle. -/
theorem not_ringAtom_C2 (j : Fin repeatUnitsX) : ¬ IsRingAtom (j, C2) :=
  not_ringAtom_of_neighbor_not_ring _ _ _ (fun z hz => (neighbors_C2 j z).mp hz)
    (not_ringAtom_OHydroxylC2 j)

/-- The reduced C3 hydroxymethyl carbon is pendant, hence on no cycle. -/
theorem not_ringAtom_C3 (j : Fin repeatUnitsX) : ¬ IsRingAtom (j, C3) :=
  not_ringAtom_of_neighbor_not_ring _ _ _ (fun z hz => (neighbors_C3 j z).mp hz)
    (not_ringAtom_OHydroxylC3 j)

/-- The C6 hydroxymethyl carbon is pendant, hence on no cycle. -/
theorem not_ringAtom_C6 (j : Fin repeatUnitsX) : ¬ IsRingAtom (j, C6) :=
  not_ringAtom_of_neighbor_not_ring _ _ _ (fun z hz => (neighbors_C6 j z).mp hz)
    (not_ringAtom_OAnhydro j)

/-- One repeat unit contributes **five** atoms to the macrocyclic ring —
the marking scheme's "the number of atoms in the macrocyclic ring for
each repeat unit is five".  The set {C1, O5, C5, C4, OGly} of unit `j` is
exactly the trace of the macrocycle's unique cycle through unit `j`:
provable by exhibiting the 35-cycle walk for `IsRingAtom` in the forward
direction and by showing every other bond is a bridge (pendant trees bear
no cycle) in the converse.  This count is a theorem consequence of graph
connectivity, not a primitive label. -/
theorem ringAtomsOfUnit_eq_five (j : Fin repeatUnitsX) : ringAtomsOfUnit j = 5 := by
  classical
  change (Finset.univ.filter (fun a => a.1 = j ∧ IsRingAtom a)).card = 5
  have hset : Finset.univ.filter (fun a : MacrocycleAtom => a.1 = j ∧ IsRingAtom a) =
      {(j, C1), (j, O5), (j, C5), (j, C4), (j, OGly)} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hr⟩
      obtain ⟨i, b⟩ := a
      change i = j at hj
      subst hj
      cases b
      · exact Or.inl rfl
      · exact absurd hr (not_ringAtom_C2 i)
      · exact absurd hr (not_ringAtom_C3 i)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact absurd hr (not_ringAtom_C6 i)
      · exact Or.inr (Or.inl rfl)
      · exact absurd hr (not_ringAtom_OAnhydro i)
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact absurd hr (not_ringAtom_OHydroxylC2 i)
      · exact absurd hr (not_ringAtom_OHydroxylC3 i)
    · obtain ⟨hC1, hO5, hC5, hC4, hOGly⟩ := ringAtoms_mem j
      rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨rfl, hC1⟩
      · exact ⟨rfl, hO5⟩
      · exact ⟨rfl, hC5⟩
      · exact ⟨rfl, hC4⟩
      · exact ⟨rfl, hOGly⟩
  rw [hset]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]

/-- One repeat unit carries **three** stereocentres: C4, C5 and the
pseudochiral acetal carbon C1 — the marking scheme's "asymmetric atoms in
the glucopyranose unit down to three".  For C4 and C5 the ligands are
constitutionally distinct; for C1 the two ring-direction ligands are
distinguished only by the retained reference labels (any automorphism of
the labelled graph exchanging them must swap the oppositely labelled
C4/C5 branches).  Provable by enumerating the stabilizer of each
candidate centre in the automorphism group of the labelled graph. -/
theorem stereocentresOfUnit_eq_three (j : Fin repeatUnitsX) :
    stereocentresOfUnit j = 3 := by
  classical
  change (Finset.univ.filter (fun a => a.1 = j ∧ IsStereocentre a)).card = 3
  have hset : Finset.univ.filter (fun a : MacrocycleAtom => a.1 = j ∧ IsStereocentre a) =
      {(j, C1), (j, C4), (j, C5)} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hj, h⟩
      rcases stereocentre_atom_types h with hb | hb | hb
      all_goals obtain ⟨i, b⟩ := a
      · change i = j at hj; change b = C1 at hb; subst hj; subst hb; exact Or.inl rfl
      · change i = j at hj; change b = C4 at hb; subst hj; subst hb
        exact Or.inr (Or.inl rfl)
      · change i = j at hj; change b = C5 at hb; subst hj; subst hb
        exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨rfl, C1_isStereocentre j⟩
      · exact ⟨rfl, C4_isStereocentre j⟩
      · exact ⟨rfl, C5_isStereocentre j⟩
  rw [hset]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]

/-- Exactly one stereocentre per unit — the acetal carbon C1 — is
pseudochiral: its two ring-direction ligands (through O5 and through the
glycosidic oxygen) are constitutionally equivalent, being exchanged by
the configuration-blind reflection automorphism, but stereochemically
distinct.  The marking scheme: "one of which (the acetal) is
pseudochiral". -/
theorem pseudochiralCentresOfUnit_eq_one (j : Fin repeatUnitsX) :
    pseudochiralCentresOfUnit j = 1 := by
  classical
  change (Finset.univ.filter (fun a => a.1 = j ∧ IsPseudochiralCentre a)).card = 1
  have hset : Finset.univ.filter (fun a : MacrocycleAtom => a.1 = j ∧
      IsPseudochiralCentre a) = {(j, C1)} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, h⟩
      rcases stereocentre_atom_types h.1 with hb | hb | hb
      all_goals obtain ⟨i, b⟩ := a
      · change i = j at hj; change b = C1 at hb; subst hj; subst hb; rfl
      · change i = j at hj; change b = C4 at hb; subst hj; subst hb
        exact absurd h (C4_not_pseudochiral i)
      · change i = j at hj; change b = C5 at hb; subst hj; subst hb
        exact absurd h (C5_not_pseudochiral i)
    · rintro rfl
      refine ⟨rfl, C1_isStereocentre j, (j, O5), (j, OGly), ?_, ?_, by simp, ?_⟩
      · exact (neighbors_C1 j (j, O5)).mpr (Or.inr (Or.inl rfl))
      · exact (neighbors_C1 j (j, OGly)).mpr (Or.inr (Or.inr rfl))
      · exact ⟨reflectionAutomorphism j, reflectAbout_self_C1 j, reflectAbout_self_O5 j⟩
  rw [hset]
  rw [Finset.card_singleton]

/-- The acetal carbon C1 of each unit is a pseudochiral centre.  C1
carries no stereochemical label: its stereogenicity follows from the
four-distinct-ligands predicate (the two ring directions are not
interchangeable by any reference-label-preserving automorphism), and its
pseudochirality from the existence of a constitutional automorphism that
does interchange them. -/
theorem acetalCarbon_isPseudochiralCentre (j : Fin repeatUnitsX) :
    IsPseudochiralCentre (j, C1) := by
  refine ⟨C1_isStereocentre j, (j, O5), (j, OGly), ?_, ?_, by simp, ?_⟩
  · exact (neighbors_C1 j (j, O5)).mpr (Or.inr (Or.inl rfl))
  · exact (neighbors_C1 j (j, OGly)).mpr (Or.inr (Or.inr rfl))
  · refine ⟨reflectionAutomorphism j, ?_, ?_⟩
    · change reflectAbout j (j, C1) = (j, C1)
      exact reflectAbout_self_C1 j
    · change reflectAbout j (j, O5) = (j, OGly)
      exact reflectAbout_self_O5 j

/-- C4 and C5 of each unit are true stereocentres (chirality centres):
their ligand triples are already constitutionally pairwise distinct. -/
theorem C4_C5_are_true_stereocentres (j : Fin repeatUnitsX) :
    IsTrueStereocentre (j, C4) ∧ IsTrueStereocentre (j, C5) :=
  ⟨⟨C4_isStereocentre j, C4_not_pseudochiral j⟩,
   ⟨C5_isStereocentre j, C5_not_pseudochiral j⟩⟩

/-- Ring-size bookkeeping: the ring atoms of X are the disjoint union over
the seven units of the per-unit ring atoms (each atom of X belongs to
exactly one unit by construction of `MacrocycleAtom`).  Provable by
`Finset.card_biUnion`/disjointness of the per-unit filters. -/
theorem ringSizeX_eq_sum_units :
    ringSizeX = ∑ j : Fin repeatUnitsX, ringAtomsOfUnit j := by
  classical
  change (Finset.univ.filter IsRingAtom).card = _
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset (Fin repeatUnitsX)))
    (f := fun a : MacrocycleAtom => a.1) (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change ((Finset.univ.filter IsRingAtom).filter (fun a => a.1 = j)).card =
    (Finset.univ.filter (fun a => a.1 = j ∧ IsRingAtom a)).card
  rw [Finset.filter_filter]
  congr 1
  ext a
  simp [and_comm]

/-- Stereocentre bookkeeping: the stereocentres of X are the disjoint
union over the seven units of the per-unit stereocentres. -/
theorem stereocentresX_eq_sum_units :
    stereocentresX = ∑ j : Fin repeatUnitsX, stereocentresOfUnit j := by
  classical
  change (Finset.univ.filter IsStereocentre).card = _
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset (Fin repeatUnitsX)))
    (f := fun a : MacrocycleAtom => a.1) (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change ((Finset.univ.filter IsStereocentre).filter (fun a => a.1 = j)).card =
    (Finset.univ.filter (fun a => a.1 = j ∧ IsStereocentre a)).card
  rw [Finset.filter_filter]
  congr 1
  ext a
  simp [and_comm]

/-- The macrocycle is achiral (the marking scheme: "the macrocycle
becomes achiral since it consists of mesobutanetetrol/glycolaldehyde
acetal units"): there is a constitutional automorphism of X — the
reflection through the midpoints of the C4–C5 bonds — that inverts the
reference label of every true stereocentre.  Pseudochiral centres are
exempt: they are not chirality centres (their two enantiomorphic ligands
are exchanged by the same reflection), which is precisely what
"pseudochiral" means. -/
def MacrocycleAchiral : Prop :=
  ∃ σ : ConstitutionalAutomorphism, ∀ c, IsTrueStereocentre c →
    ∃ b, configLabel c = some b ∧ configLabel (σ.toEquiv c) = some !b

/-- The assembled macrocycle X is achiral. -/
theorem macrocycle_achiral : MacrocycleAchiral := by
  refine ⟨reflectionAutomorphism 0, fun c hc => ?_⟩
  obtain ⟨i, b⟩ := c
  obtain ⟨hel, hh, -, -⟩ := hc.1
  cases b
  · -- the acetal carbon: pseudochiral, hence not a true stereocentre
    exact absurd (acetalCarbon_isPseudochiralCentre i) hc.2
  · exact absurd hh (by simp [macrocycleLabel, labelX])
  · exact absurd hh (by simp [macrocycleLabel, labelX])
  · -- C4 ↦ C5 of a reflected unit: some false ↦ some true
    exact ⟨false, rfl, rfl⟩
  · -- C5 ↦ C4 of a reflected unit: some true ↦ some false
    exact ⟨true, rfl, rfl⟩
  · exact absurd hh (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])
  · exact absurd hel (by simp [macrocycleLabel, labelX])

/-- **T9.3 target.**  The ring size of macrocycle X is `rs = 35` and the
number of stereocentres in X is `sc = 21`: seven meso repeat units, five
ring atoms and three stereocentres apiece.  Provable from
`ringSizeX_eq_sum_units`, `ringAtomsOfUnit_eq_five`,
`stereocentresX_eq_sum_units` and `stereocentresOfUnit_eq_three` by
`Finset.sum_const`/`Finset.card_univ`. -/
theorem icho_2026_t9_a3 : ringSizeX = 35 ∧ stereocentresX = 21 := by
  constructor
  · rw [ringSizeX_eq_sum_units]
    simp only [ringAtomsOfUnit_eq_five, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    decide
  · rw [stereocentresX_eq_sum_units]
    simp only [stereocentresOfUnit_eq_three, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    decide

end IChO2026.T9.A3
