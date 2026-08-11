import Mathlib

/-!
# IChO 2026, Theory Problem 3, Part 3.6 — π–π stacking energies of COF-8

Source: 58th International Chemistry Olympiad, Tashkent 2026, Theory
Problem 3 ("Into Reticular Chemistry"), question 3.6; question page 6
(`T3_page-6.png`), marking scheme table for 3.6.

## Source contract

**Given (sourced data).** The problem's interaction table lists, in
`kJ mol⁻¹`, the π–π interaction energy of a face-to-face pair of aromatic
rings in two stacking geometries — the eclipsed (sandwich) contact and the
slipped ("slightly shifted") contact:

| contact              | eclipsed | slipped |
|----------------------|----------|---------|
| benzene–benzene (b-b)   | −7.9  | −12.6 |
| benzene–triazine (b-t)  | −49.8 | −55.6 |
| triazine–triazine (t-t) | −6.7  | −16.7 |

COF-8 is synthesised from (E1 + D2) and has the hexagonal-2 topology; one
repeat unit contains four benzene rings and one triazine ring as its only
aromatic units. The problem states that the AA′ slightly shifted mode of a
COF-8 bilayer has a π–π stacking interaction energy of −67.1 kJ mol⁻¹
between two layers of one repeat unit; the model below reproduces this
value, which anchors the contact counting.

**Assumption (stated in the question).** π–π stacking happens only between
aromatic units: contacts involving non-aromatic linker content contribute
no energy.

**Governing relation.** The bilayer stacking energy of one repeat-unit pair
is the sum of the pairwise contact energies over the contacts made between
the two layers (pairwise additivity, as used by the marking scheme).

**Chemical model (read off the structures by the marking scheme).** In the
in-registry arrangements AA and AA′ each aromatic ring faces the identical
ring of the other layer, giving 4 benzene–benzene and 1 triazine–triazine
contacts per repeat-unit pair (eclipsed for AA, slipped for AA′). In the
offset arrangements AB and AB′ a repeat-unit pair makes a single
benzene–triazine contact (eclipsed for AB, slipped for AB′).

**Requested conclusions.** The stacking energies of the AA, AB and AB′
arrangements. These appear only as theorem conclusions; no definition below
contains a requested total energy.
-/

namespace IChO2026Problems.T3.A6

/-- A molar π–π stacking energy readout in `kJ mol⁻¹`, the unit of the
problem's interaction table. -/
abbrev KJPerMol := ℝ

/-- The aromatic ring types that make π–π contacts in COF-8: benzene
(X = CH in the problem's table) and 1,3,5-triazine (X = N). -/
inductive AromaticRing where
  | benzene
  | triazine
  deriving DecidableEq, Repr

/-- The two interaction geometries distinguished in the problem's energy
table: the eclipsed, face-to-face contact (left table column) and the
slipped, "slightly shifted" contact (right table column). -/
inductive StackingGeometry where
  | eclipsed
  | slipped
  deriving DecidableEq, Repr

/-- The constituents of a COF-8 repeat unit as seen by the stacking model:
an aromatic ring, or the non-aromatic linker content (the vinylene bridges
and nitrile groups). The question's assumption that π–π stacking happens
only between aromatic units is what makes the second case carry no π–π
interaction energy. -/
inductive RepeatUnitPart where
  | aromaticRing (ring : AromaticRing)
  | linker
  deriving DecidableEq, Repr

/-- The π–π interaction energy, in kJ mol⁻¹, between two repeat-unit parts
facing each other across the bilayer in a given stacking geometry.

For two aromatic rings this is the value tabulated in the problem:
benzene–benzene −7.9 (eclipsed) / −12.6 (slipped), benzene–triazine
−49.8 / −55.6, triazine–triazine −6.7 / −16.7. A benzene–triazine contact
is the same physical contact whichever layer supplies the benzene ring, so
both orders carry the same value. Any contact involving non-aromatic linker
content is zero — the question's standing assumption that π–π stacking
happens only between aromatic units. -/
def facingEnergy : RepeatUnitPart → RepeatUnitPart → StackingGeometry → KJPerMol
  | .aromaticRing .benzene, .aromaticRing .benzene, .eclipsed => -7.9
  | .aromaticRing .benzene, .aromaticRing .benzene, .slipped => -12.6
  | .aromaticRing .benzene, .aromaticRing .triazine, .eclipsed => -49.8
  | .aromaticRing .benzene, .aromaticRing .triazine, .slipped => -55.6
  | .aromaticRing .triazine, .aromaticRing .benzene, .eclipsed => -49.8
  | .aromaticRing .triazine, .aromaticRing .benzene, .slipped => -55.6
  | .aromaticRing .triazine, .aromaticRing .triazine, .eclipsed => -6.7
  | .aromaticRing .triazine, .aromaticRing .triazine, .slipped => -16.7
  | _, _, _ => 0

/-- One face-to-face contact between a part of one layer's repeat unit and a
part of the other layer's repeat unit, in a given stacking geometry. -/
structure BilayerContact where
  upper : RepeatUnitPart
  lower : RepeatUnitPart
  geometry : StackingGeometry

/-- The total π–π stacking energy between two layers of one repeat unit, in
kJ mol⁻¹: the sum of the pairwise contact energies. This pairwise-additive
reading of the interaction table is the governing relation used by the
problem's marking scheme. -/
def stackingEnergy (contacts : List BilayerContact) : KJPerMol :=
  (contacts.map fun c => facingEnergy c.upper c.lower c.geometry).sum

/-- The aromatic rings of one COF-8 repeat unit: four benzene rings and one
triazine ring. COF-8 has the hexagonal-2 topology built from E1 + D2; its
repeat unit comprises one E1 core (a benzene ring) and one D2 core (a
central triazine ring bearing three phenylene benzene rings). Every other
repeat-unit constituent is non-aromatic linker content. -/
def cof8AromaticContent : Multiset AromaticRing :=
  {.benzene, .benzene, .benzene, .benzene, .triazine}

/-- One COF-8 repeat unit contains four benzene rings. -/
theorem cof8AromaticContent_benzene :
    cof8AromaticContent.count AromaticRing.benzene = 4 := by
  decide

/-- One COF-8 repeat unit contains one triazine ring. -/
theorem cof8AromaticContent_triazine :
    cof8AromaticContent.count AromaticRing.triazine = 1 := by
  decide

/-- The stacking arrangements of a COF-8 bilayer named in part 3.6 and in
the problem statement: the in-registry arrangement AA and its "slightly
shifted" variant AA′, and the offset arrangement AB and its slightly
shifted variant AB′. -/
inductive StackingArrangement where
  | AA
  | AA'
  | AB
  | AB'
  deriving DecidableEq, Repr

/-- The contacts made between two layers of one COF-8 repeat unit in each
stacking arrangement, as read off the repeat-unit structures in the marking
scheme: four benzene–benzene contacts and one triazine–triazine contact for
the in-registry arrangements AA (eclipsed) and AA′ (slipped), and a single
benzene–triazine contact for the offset arrangements AB (eclipsed) and AB′
(slipped). Contacts with non-aromatic linker content contribute nothing and
are therefore not listed (see `facingEnergy_eq_zero_of_linker`). -/
def contactPattern : StackingArrangement → List BilayerContact
  | .AA =>
      [ ⟨.aromaticRing .benzene, .aromaticRing .benzene, .eclipsed⟩,
        ⟨.aromaticRing .benzene, .aromaticRing .benzene, .eclipsed⟩,
        ⟨.aromaticRing .benzene, .aromaticRing .benzene, .eclipsed⟩,
        ⟨.aromaticRing .benzene, .aromaticRing .benzene, .eclipsed⟩,
        ⟨.aromaticRing .triazine, .aromaticRing .triazine, .eclipsed⟩ ]
  | .AA' =>
      [ ⟨.aromaticRing .benzene, .aromaticRing .benzene, .slipped⟩,
        ⟨.aromaticRing .benzene, .aromaticRing .benzene, .slipped⟩,
        ⟨.aromaticRing .benzene, .aromaticRing .benzene, .slipped⟩,
        ⟨.aromaticRing .benzene, .aromaticRing .benzene, .slipped⟩,
        ⟨.aromaticRing .triazine, .aromaticRing .triazine, .slipped⟩ ]
  | .AB =>
      [ ⟨.aromaticRing .benzene, .aromaticRing .triazine, .eclipsed⟩ ]
  | .AB' =>
      [ ⟨.aromaticRing .benzene, .aromaticRing .triazine, .slipped⟩ ]

/-- The question's standing assumption, in eliminative form: a contact in
which at least one side is non-aromatic linker content carries no π–π
interaction energy, whatever the stacking geometry. -/
theorem facingEnergy_eq_zero_of_linker
    (upper lower : RepeatUnitPart) (geometry : StackingGeometry)
    (h : upper = .linker ∨ lower = .linker) :
    facingEnergy upper lower geometry = 0 := by
  rcases h with rfl | rfl
  · cases lower <;> cases geometry <;> rfl
  · cases upper
    case linker => cases geometry <;> rfl
    case aromaticRing r => cases r <;> cases geometry <;> rfl

/-- Consistency anchor, stated in the problem: the AA′ slightly shifted mode
of a COF-8 bilayer has stacking energy −67.1 kJ mol⁻¹ between two layers of
one repeat unit. The model reproduces the stated value as
4 · (−12.6) + 1 · (−16.7). -/
theorem cof8_stackingEnergy_AA' :
    stackingEnergy (contactPattern .AA') = -67.1 := by
  norm_num [stackingEnergy, contactPattern, facingEnergy]

/-- Part 3.6, AA arrangement: 4 · (−7.9) + 1 · (−6.7) = −38.3 kJ mol⁻¹. -/
theorem cof8_stackingEnergy_AA :
    stackingEnergy (contactPattern .AA) = -38.3 := by
  norm_num [stackingEnergy, contactPattern, facingEnergy]

/-- Part 3.6, AB arrangement: 1 · (−49.8) = −49.8 kJ mol⁻¹. -/
theorem cof8_stackingEnergy_AB :
    stackingEnergy (contactPattern .AB) = -49.8 := by
  norm_num [stackingEnergy, contactPattern, facingEnergy]

/-- Part 3.6, AB′ arrangement: 1 · (−55.6) = −55.6 kJ mol⁻¹. -/
theorem cof8_stackingEnergy_AB' :
    stackingEnergy (contactPattern .AB') = -55.6 := by
  norm_num [stackingEnergy, contactPattern, facingEnergy]

end IChO2026Problems.T3.A6
