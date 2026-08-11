import Mathlib

/-!
# IChO 2026, Theory Problem T4, subquestion 4.4 — energy released in ²³⁵U fission

Source: 58th International Chemistry Olympiad, Tashkent 2026, Theory problem
T4 ("The nuclear past of Uzbekistan"), subquestion 4.4 (2 pt).  Visual
evidence: `T4_page-1.png` (shared context: the chain reaction
`²³⁵U + ¹n → … + 3 ¹n`) and `T4_page-2.png` (the statement of 4.4).

## Subquestion

Calculate the energy released in this reaction (`ΔE`, MeV), if the binding
energy `BE(²³⁵U) = 7.59 MeV/nucleon` and the average binding energy for
fission products `BE(fis.) = 8.45 MeV/nucleon`.  *Neglect* the binding energy
of free neutrons.

## Assumption / target split

Assumptions (all sourced, none of them the requested answer):

* `hbeU`, `hbeFis` — the two binding energies per nucleon printed in 4.4;
* `hmassU` — the fissioning nucleus is ²³⁵U, mass number 235 (shared context);
* `hneutrons` — three neutrons are released (shared context, `… + 3 ¹n`);
* `hmass` — mass-number conservation for the reaction `²³⁵U + ¹n → fragments +
  3 ¹n`, i.e. `ΣA(fragments) + 3 = 235 + 1`; the `+ 1` is the single absorbed
  neutron of mass number 1;
* the neglect of the free neutrons' binding energy, encoded in
  `FissionEnergyBudget.energyReleased` (free neutrons carry no binding-energy
  term).

Target (the requested conclusion, not assumed anywhere):

* `ΔE = 185.2 MeV`, i.e. `8.45 · 233 − 7.59 · 235`.

## Previous-part bridge (T4-A3)

T4-A3 established the fission equation `²³⁵U + ¹n → ⁹³Rb + ¹⁴⁰Cs + 3 ¹n` and
the total fragment mass number `ΣA = 235 + 1 − 3 = 233`.  Its dependency
policy is `natural_language_prerequisite_only`, so that conclusion is restated
here through the explicit hypotheses `hneutrons` and `hmass` (from which
`massFragments = 233` is derived); no generated problem file is imported, and
the identity of the fragments (Rb/Cs) does not affect this subquestion's
numerical conclusion, so only the conserved nucleon count is carried over.

## Numerical convention

Following the project convention (see `IChO2026Chem.Kinetics.BelousovZhabotinsky`),
energies and binding energies per nucleon are represented by their real
numerical readouts in the source's units (MeV and MeV/nucleon).  Neither
Mathlib, Physlib, nor the CRNT chemistry library exposes a nuclear
binding-energy or isotope API, so the smallest faithful local interface is
kept here.
-/

namespace IChO2026Problems.T4A4

/-- A binding energy per nucleon, as its numerical readout in `MeV/nucleon`. -/
abbrev BindingEnergyPerNucleon := ℝ

/-- An energy, as its numerical readout in `MeV` (the unit requested for `ΔE`). -/
abbrev EnergyMeV := ℝ

/-- The binding-energy budget of the neutron-induced fission of ²³⁵U,
`²³⁵U + ¹n → fission fragments + 3 ¹n`.

Only the data entering the energy balance are recorded: the binding energy per
nucleon and mass number of the fissioning nucleus, the average binding energy
per nucleon and total mass number of the fission fragments, and the number of
free neutrons released (whose binding energy the problem says to neglect). -/
structure FissionEnergyBudget where
  /-- Binding energy per nucleon of the fissioning nucleus ²³⁵U (`MeV/nucleon`). -/
  beNucleus : BindingEnergyPerNucleon
  /-- Mass number of the fissioning nucleus (235 for ²³⁵U). -/
  massNucleus : ℕ
  /-- Average binding energy per nucleon of the fission fragments (`MeV/nucleon`). -/
  beFragments : BindingEnergyPerNucleon
  /-- Total mass number carried by the fission fragments (`ΣA = 233` from T4-A3). -/
  massFragments : ℕ
  /-- Number of free neutrons released (3); their binding energy is neglected. -/
  freeNeutrons : ℕ

/-- The energy released by the fission, in MeV: the total binding energy of
the fission fragments minus the total binding energy of the fissioning ²³⁵U
nucleus.  A nucleus of mass number `A` with binding energy `BE` per nucleon
has total binding energy `BE · A`.  Free neutrons — the absorbed neutron on
the reactant side and the emitted ones on the product side — carry no
binding-energy term, as the problem instructs ("neglect the binding energy of
free neutrons").  Positive `ΔE` means energy is released. -/
def FissionEnergyBudget.energyReleased (d : FissionEnergyBudget) : EnergyMeV :=
  d.beFragments * d.massFragments - d.beNucleus * d.massNucleus

/-- The total mass number of the fission fragments: mass-number conservation
for `²³⁵U + ¹n → fragments + 3 ¹n` forces `ΣA = 235 + 1 − 3 = 233`.  This is
the reusable T4-A3 conclusion, recovered from the explicit conservation
hypothesis rather than assumed. -/
theorem FissionEnergyBudget.massFragments_eq (d : FissionEnergyBudget)
    (hmassU : d.massNucleus = 235) (hneutrons : d.freeNeutrons = 3)
    (hmass : d.massFragments + d.freeNeutrons = d.massNucleus + 1) :
    d.massFragments = 233 := by
  omega

/-- **IChO 2026, T4, subquestion 4.4.**  With `BE(²³⁵U) = 7.59 MeV/nucleon`,
average `BE(fis.) = 8.45 MeV/nucleon`, and neglected free-neutron binding
energy, the energy released by the fission reaction is
`ΔE = 8.45 · 233 − 7.59 · 235 = 185.2 MeV`. -/
theorem energy_released (d : FissionEnergyBudget)
    (hbeU : d.beNucleus = 7.59)
    (hbeFis : d.beFragments = 8.45)
    (hmassU : d.massNucleus = 235)
    (hneutrons : d.freeNeutrons = 3)
    (hmass : d.massFragments + d.freeNeutrons = d.massNucleus + 1) :
    d.energyReleased = 185.2 := by
  have hfrags : d.massFragments = 233 := d.massFragments_eq hmassU hneutrons hmass
  unfold FissionEnergyBudget.energyReleased
  rw [hbeU, hbeFis, hmassU, hfrags]
  norm_num

end IChO2026Problems.T4A4
