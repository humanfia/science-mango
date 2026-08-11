import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T6, Subquestion 6.7 — global aromaticity of the porphyrin nanoring P6

## Source contract

58th International Chemistry Olympiad, Tashkent 2026, Theory problem T6
("Carbon Nanorings"), printed question page 5 (problem PDF page 56); marking
scheme on solution PDF page 58.

When aromatic rings are joined to form a macrocycle, oxidation or reduction can
produce *global aromaticity*: π electrons delocalise around the entire
macrocycle, and **only** the π system forming the continuous conjugated pathway
around the ring participates (the "bold pathway" of the statement). P6 is the
porphyrin nanobelt of part 6.6: six zinc-porphyrin subunits linked by butadiyne
bridges into a single macrocycle (T6 page 4 figure, bracket subscript 6).

**Question 6.7.** Based on Hückel's rule, find the minimum number of electrons,
`n(e)`, that should be removed from P6 to achieve global aromaticity, and write
the total number of π electrons, `n(t)`, in the resulting global aromatic
system.

## Transparent carrier for the per-subunit count

The per-subunit π-electron count is **not** stipulated.  The marking-scheme
figure (solution PDF page 58) draws the abbreviated P6 subunit with the global
conjugated pathway **highlighted in red**, and instructs to "count electrons
around the abbreviated structure of P6".  Inspection of that figure identifies,
per subunit, seven red-highlighted two-electron π features along the pathway
(the single bonds connecting them carry the σ framework of the circuit and
contribute no π electrons):

1. the left butadiyne-linker triple bond at the left meso position — one of its
   two π pairs lies in the conjugation plane of the macrocycle (the other is
   orthogonal and does not participate): 2 electrons;
2. the left meso=α C=C bond entering the lower-left pyrrole: 2 electrons;
3. the β=β′ C=C bond of the lower-left pyrrole: 2 electrons;
4. the α=meso C=C bond from the lower-left pyrrole to the lower meso carbon:
   2 electrons;
5. the α=N double bond of the lower-right pyrrole, where the highlighted
   circuit crosses the inner nitrogen edge: 2 electrons;
6. the α′=meso C=C bond from the lower-right pyrrole to the right meso carbon:
   2 electrons;
7. the right butadiyne-linker triple bond at the right meso position — one
   π pair as in (1): 2 electrons.

These seven features are enumerated as the list `p6SubunitCensus` over the
inductive `PathwayPiFeature`; the per-subunit count `p6SubunitPiElectrons` is
*defined* as the sum of their electron counts, and the chain

`7 features × 2 e⁻ = 14` per subunit → `6 × 14 = 84` ground-state total
(`84 = 4 · 21`, Hückel anti-aromatic) → least removal `n(e) = 2` →
`n(t) = 82 = 4 · 20 + 2`

is proved theorem by theorem.  Neither `14` nor `84` appears as a premise.

## Assumption / target split

Assumptions (sourced data, *not* the requested answer):

* Hückel's rule, encoded as `IsHuckelAromatic` (count `= 4k + 2`) and
  `IsHuckelAntiAromatic` (count `= 4k`, `k ≥ 1`) — the governing law named by
  the problem.
* The structural data of P6: six porphyrin subunits (visible in the P6 figure
  on T6 page 4, bracket subscript 6), and the seven-item per-subunit census of
  red-highlighted two-electron π features read off the marking-scheme figure
  (solution PDF page 58) — chemical structure and counting *instructions*,
  distinct from the requested outputs `n(e)` and `n(t)`.

Targets (the requested conclusions, proved from the above):

* the per-subunit pathway carries 14 π electrons (`p6_subunit_pi_electrons`);
* the ground-state global pathway of P6 carries 84 π electrons
  (`P6_groundState_pi_electrons`) and is Hückel anti-aromatic
  (`P6_groundState_global_anti_aromatic`, since `84 = 4 · 21`);
* the minimum number of electrons to remove so that the remaining global
  π system is Hückel aromatic is `n(e) = 2` (`P6_least_removal_two`), and the
  resulting total is `n(t) = 82 = 4 · 20 + 2`
  (`P6_aromatic_total_after_least_removal`, `icho_2026_t6_a7_target`).

Oxidation is modeled as subtraction of electrons from the ground-state count;
natural truncated subtraction is harmless because every count `≤ 0` reachable
by over-oxidation fails the `4k + 2` test anyway.
-/

namespace Icho2026T6A7

/-- **Hückel's rule (aromaticity).** A monocyclic, fully conjugated π system is
aromatic when its π-electron count equals `4k + 2` for some natural `k`.
Here the count is taken along the single continuous conjugated pathway that
participates in the global delocalisation, as specified by the problem. -/
def IsHuckelAromatic (electronCount : ℕ) : Prop :=
  ∃ k : ℕ, electronCount = 4 * k + 2

/-- **Hückel anti-aromaticity.** A monocyclic, fully conjugated π system is
anti-aromatic when its π-electron count is a positive multiple of four
(`4k` with `k ≥ 1`). The problem notes that oxidised P6 can exhibit both
global aromaticity and global anti-aromaticity, so both predicates belong to
the vocabulary of this part. -/
def IsHuckelAntiAromatic (electronCount : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ electronCount = 4 * k

/-- **A two-electron π feature of the global conjugated pathway.**
The marking-scheme figure (solution PDF page 58) highlights the participating
π system of one P6 subunit in red; every highlighted feature is one of the
following chemically identified kinds, each contributing one π pair to the
single continuous conjugated circuit around the macrocycle. -/
inductive PathwayPiFeature where
  /-- One π pair of a butadiyne-linker triple bond (`C≡C`) at a linker-bearing
  meso position. A triple bond holds two π pairs; only the pair lying in the
  conjugation plane of the macrocycle participates in the global circuit, the
  orthogonal pair does not — hence one pair (2 electrons) per linker. -/
  | alkynePiPair
  /-- A `C=C` double bond of the porphyrin perimeter lying on the highlighted
  pathway (the meso=α, β=β′ and α=meso bonds of the lower arc). -/
  | perimeterAlkeneCC
  /-- The `C=N` double bond on the inner edge of a pyrroline nitrogen where the
  highlighted circuit crosses the inside of the porphyrin (lower-right pyrrole
  of the marking-scheme figure). -/
  | perimeterImineCN

namespace PathwayPiFeature

/-- π electrons contributed by one highlighted pathway feature. Every feature
of the census is a two-electron feature (one π pair). -/
def piElectrons : PathwayPiFeature → ℕ
  | .alkynePiPair => 2
  | .perimeterAlkeneCC => 2
  | .perimeterImineCN => 2

end PathwayPiFeature

/-- **The per-subunit census.** The seven red-highlighted two-electron π
features of one P6 subunit, listed in the order in which the highlighted
circuit traverses them (solution PDF page 58 figure), from the left linker
around the lower arc of the porphyrin to the right linker. The connecting
single bonds along the arc carry no π electrons and are not listed. -/
def p6SubunitCensus : List PathwayPiFeature :=
  [ .alkynePiPair,      -- left butadiyne linker at the left meso position, one π pair
    .perimeterAlkeneCC, -- left meso=α, entering the lower-left pyrrole
    .perimeterAlkeneCC, -- β=β′ of the lower-left pyrrole
    .perimeterAlkeneCC, -- α=lower meso, lower-left pyrrole to the lower meso carbon
    .perimeterImineCN,  -- α=N, inner edge of the lower-right pyrrole
    .perimeterAlkeneCC, -- α′=right meso, lower-right pyrrole to the right meso carbon
    .alkynePiPair ]     -- right butadiyne linker at the right meso position, one π pair

/-- The census of one subunit comprises exactly seven highlighted π features. -/
theorem p6_subunit_census_has_seven_features : p6SubunitCensus.length = 7 :=
  rfl

/-- **Per-subunit π-electron count**, defined as the sum of the electron
contributions of the seven census features — never stipulated as a literal. -/
def p6SubunitPiElectrons : ℕ :=
  (p6SubunitCensus.map PathwayPiFeature.piElectrons).sum

/-- The seven two-electron features of the census sum to 14 π electrons per
subunit — the counting step the marking scheme records as "14 × 6". -/
theorem p6_subunit_pi_electrons : p6SubunitPiElectrons = 14 := by
  decide

/-- A porphyrin-based nanoring: `porphyrinUnits` identical porphyrin subunits
joined into one macrocycle, where each subunit contributes
`piElectronsPerUnit` π electrons to the single continuous conjugated pathway
around the ring (the only π system that participates in global aromaticity). -/
structure PorphyrinNanoring where
  /-- Number of porphyrin subunits forming the macrocycle. -/
  porphyrinUnits : ℕ
  /-- π electrons contributed by one subunit to the global conjugated pathway. -/
  piElectronsPerUnit : ℕ

namespace PorphyrinNanoring

/-- Total π-electron count of the global conjugated pathway in the ground
(uncharged) state: the per-subunit contribution summed over all subunits. -/
def groundStatePiElectrons (ring : PorphyrinNanoring) : ℕ :=
  ring.porphyrinUnits * ring.piElectronsPerUnit

/-- π-electron count of the global pathway after oxidation removes `removed`
electrons. (Truncated subtraction: more electrons cannot be removed than the
pathway holds; any resulting count of `0` is neither aromatic nor relevant.) -/
def piElectronsAfterOxidation (ring : PorphyrinNanoring) (removed : ℕ) : ℕ :=
  ring.groundStatePiElectrons - removed

end PorphyrinNanoring

/-- The nanoring **P6** of question 6.7: six zinc-porphyrin subunits linked by
butadiyne bridges into a belt (structure figure on T6 page 4, bracket
subscript `6`). The per-subunit contribution is the census sum
`p6SubunitPiElectrons` — the enumerated seven red-highlighted two-electron
features of the marking-scheme figure — not a stipulated literal. -/
def P6 : PorphyrinNanoring where
  porphyrinUnits := 6
  piElectronsPerUnit := p6SubunitPiElectrons

/-- The global conjugated pathway of ground-state P6 carries `6 × 14 = 84`
π electrons, computed from the per-subunit census. -/
theorem P6_groundState_pi_electrons : P6.groundStatePiElectrons = 84 := by
  decide

/-- In its ground state the global pathway of P6 holds `84 = 4 · 21` π
electrons, a Hückel anti-aromatic (`4k`) count — so oxidation is required to
reach an aromatic count. -/
theorem P6_groundState_global_anti_aromatic :
    IsHuckelAntiAromatic P6.groundStatePiElectrons :=
  ⟨21, by decide, by decide⟩

/-- **Least oxidation to aromaticity.** Removing two electrons is the minimum
that makes the remaining global π system Hückel aromatic: two electrons
suffice (`84 − 2 = 82 = 4 · 20 + 2`), and no smaller removal works, since
`84 − m = 4k + 2` forces `m ≥ 2` (removing zero leaves the anti-aromatic
count 84, and removing one leaves 83, which is neither `4k` nor `4k + 2`). -/
theorem P6_least_removal_two :
    IsLeast {m : ℕ | IsHuckelAromatic (P6.piElectronsAfterOxidation m)} 2 := by
  constructor
  · exact ⟨20, by decide⟩
  · intro m hm
    obtain ⟨k, hk⟩ := hm
    have h84 : P6.groundStatePiElectrons = 84 := P6_groundState_pi_electrons
    unfold PorphyrinNanoring.piElectronsAfterOxidation at hk
    rw [h84] at hk
    omega

/-- **The aromatic total.** After the least removal of two electrons, the
global aromatic system carries `n(t) = 82` π electrons, and
`82 = 4 · 20 + 2` indeed satisfies Hückel's `4k + 2` rule. -/
theorem P6_aromatic_total_after_least_removal :
    P6.piElectronsAfterOxidation 2 = 82 ∧
      IsHuckelAromatic (P6.piElectronsAfterOxidation 2) :=
  ⟨by decide, 20, by decide⟩

/-- **Problem 6.7 (target).** The minimum number of electrons that must be
removed from P6 so that the remaining global π system satisfies Hückel's
`4k + 2` rule is `n(e) = 2`, and the total number of π electrons in the
resulting global aromatic system is `n(t) = 82`. Both requested outputs appear
as conclusions only, derived from the census of highlighted pathway features. -/
theorem icho_2026_t6_a7_target :
    IsLeast {m : ℕ | IsHuckelAromatic (P6.piElectronsAfterOxidation m)} 2 ∧
      P6.piElectronsAfterOxidation 2 = 82 :=
  ⟨P6_least_removal_two, P6_aromatic_total_after_least_removal.1⟩

end Icho2026T6A7
