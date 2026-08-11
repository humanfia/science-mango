import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T3-A6: π-π stacking energies of COF-8

Energies in this file are numerical values in `kJ mol⁻¹`.  The source's
assumption that π-π stacking happens only between aromatic units is built into
`AromaticPair`: it has exactly the benzene--benzene, benzene--triazine, and
triazine--triazine cases.  Thus a contact counted by `COF8StackingData` cannot
silently denote a non-aromatic interaction.
-/

namespace IChO2026Problems.T3A6

/-- The two aromatic ring species in the repeat unit of the named sample
COF-8. -/
private inductive AromaticRing where
  | benzene
  | triazine
  deriving DecidableEq, Fintype, Repr

/-- The unordered aromatic ring pairs distinguished in the supplied energy
table.  No non-aromatic pair is admitted here. -/
private inductive AromaticPair where
  | benzeneBenzene
  | benzeneTriazine
  | triazineTriazine
  deriving DecidableEq, Fintype, Repr

/-- The two interaction geometries represented by the left and right energy
columns in the source figure.  The latter is the shifted/slipped geometry used
in the primed stacking modes. -/
private inductive InteractionGeometry where
  | unshifted
  | shifted
  deriving DecidableEq, Repr

/-- The four bilayer arrangements displayed for the COF layers.  The current
subquestion requests the energies of `aa`, `ab`, and `abPrime`; `aaPrime` is
included because its observed energy is supplied in the question. -/
private inductive StackingMode where
  | aa
  | aaPrime
  | ab
  | abPrime
  deriving DecidableEq, Repr

/-- The interaction geometry assigned by the source diagrams to each stacking
mode. -/
private def StackingMode.geometry : StackingMode → InteractionGeometry
  | .aa | .ab => .unshifted
  | .aaPrime | .abPrime => .shifted

/-- Numerical π-π interaction energy in the source's `kJ mol⁻¹` scale. -/
private abbrev StackingEnergy := ℝ

/-- The empirical interaction-energy table.  It is separate from the COF-8
contact inventory so that the requested totals are obtained by summation. -/
private structure InteractionEnergyTable where
  energy : InteractionGeometry → AromaticPair → StackingEnergy

/-- The six empirical energy measurements read from the table in the source
figure. -/
private def InteractionEnergyTable.matchesSourceTable
    (table : InteractionEnergyTable) : Prop :=
  table.energy .unshifted .benzeneBenzene = -7.9 ∧
    table.energy .shifted .benzeneBenzene = -12.6 ∧
      table.energy .unshifted .benzeneTriazine = -49.8 ∧
        table.energy .shifted .benzeneTriazine = -55.6 ∧
          table.energy .unshifted .triazineTriazine = -6.7 ∧
            table.energy .shifted .triazineTriazine = -16.7

/-- COF-8's aromatic repeat-unit inventory and its interlayer aromatic
contacts for each displayed stacking mode.  Counts are natural numbers because
they count ring-pair contacts between two layers of one repeat unit. -/
private structure COF8StackingData where
  aromaticRingCount : AromaticRing → ℕ
  contactCount : StackingMode → AromaticPair → ℕ

/-- The ring inventory and aromatic contact counts obtained from the COF-8
repeat-unit and stacking diagrams.  In particular, this does not contain any
of the three totals requested by T3-A6. -/
private def COF8StackingData.matchesSourceDiagram
    (data : COF8StackingData) : Prop :=
  data.aromaticRingCount .benzene = 4 ∧
    data.aromaticRingCount .triazine = 1 ∧
      data.contactCount .aa .benzeneBenzene = 4 ∧
        data.contactCount .aa .benzeneTriazine = 0 ∧
          data.contactCount .aa .triazineTriazine = 1 ∧
            data.contactCount .aaPrime .benzeneBenzene = 4 ∧
              data.contactCount .aaPrime .benzeneTriazine = 0 ∧
                data.contactCount .aaPrime .triazineTriazine = 1 ∧
                  data.contactCount .ab .benzeneBenzene = 0 ∧
                    data.contactCount .ab .benzeneTriazine = 1 ∧
                      data.contactCount .ab .triazineTriazine = 0 ∧
                        data.contactCount .abPrime .benzeneBenzene = 0 ∧
                          data.contactCount .abPrime .benzeneTriazine = 1 ∧
                            data.contactCount .abPrime .triazineTriazine = 0

/-- Add the energy of each aromatic interlayer contact for one repeat unit of
the named COF-8 bilayer in the specified stacking mode. -/
noncomputable def cof8StackingEnergy (table : InteractionEnergyTable)
    (data : COF8StackingData) (mode : StackingMode) : StackingEnergy :=
  ∑ pair : AromaticPair,
    (data.contactCount mode pair : ℝ) * table.energy mode.geometry pair

/-- The independently supplied observation for the slightly shifted AA' COF-8
bilayer.  It records a measured energy, rather than using an answer to the
current AA/AB/AB' calculation as a premise. -/
private def isObservedAAPrimeEnergy (table : InteractionEnergyTable)
    (data : COF8StackingData) : Prop :=
  cof8StackingEnergy table data .aaPrime = -67.1

/--
From the supplied π-π interaction table and the aromatic contact counts in
one COF-8 repeat unit, the stacking energies requested for the AA, AB, and
AB' arrangements are respectively `-38.3`, `-49.8`, and `-55.6 kJ mol⁻¹`.
The AA' observation is retained as source data but is not one of the requested
outputs.
-/
theorem cof8_AA_AB_ABPrime_stacking_energies
    (table : InteractionEnergyTable) (data : COF8StackingData)
    (htable : table.matchesSourceTable)
    (hdiagram : data.matchesSourceDiagram)
    (haaPrime : isObservedAAPrimeEnergy table data) :
    cof8StackingEnergy table data .aa = -38.3 ∧
      cof8StackingEnergy table data .ab = -49.8 ∧
        cof8StackingEnergy table data .abPrime = -55.6 := by
  rcases htable with ⟨hbb, hbb', hbt, hbt', htt, htt'⟩
  rcases hdiagram with
    ⟨hringB, hringT, haaBB, haaBT, haaTT, haa'BB, haa'BT, haa'TT,
      habBB, habBT, habTT, hab'BB, hab'BT, hab'TT⟩
  have h_pairs : (Finset.univ : Finset AromaticPair) =
      {.benzeneBenzene, .benzeneTriazine, .triazineTriazine} := by
    decide
  simp [h_pairs, StackingMode.geometry, cof8StackingEnergy,
    hbb, hbb', hbt, hbt', htt, htt',
    haaBB, haaBT, haaTT, habBB, habBT, habTT, hab'BB, hab'BT, hab'TT]
  norm_num

end IChO2026Problems.T3A6
