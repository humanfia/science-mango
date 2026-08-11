import Mathlib

/-!
# IChO 2026, Theory Problem T6, Subquestion 6.4 — Carbon Nanorings:
  identity of the four intense ESI mass-spectrum peaks

## Source contract (58th IChO, Tashkent 2026, problem PDF page 53)

In 2025 the first relatively stable cyclo[48]carbon was synthesised,
stabilised by catenation (interlocking rings) with macrocycle **E**, and first
characterised by electrospray mass spectrometry **in positive mode**.  The
source figure prints the structure of E together with its molecular formula
**C₄₀H₃₄N₂O₃** (image `T6_page-2.png`).  Subquestion 6.4 states:

> In the mass spectrum obtained, four intense peaks were observed m/z: 591,
> 783, 879, and 1174.  **Suggest** the identity of these ions.  **Use**
> integer atomic masses and **assume** no fragmentation happened.  The ion
> corresponding to m/z = 591 is given as an example.

### Inventory

* Species: cyclo[48]carbon C₄₈; macrocycle E = C₄₀H₃₄N₂O₃; catenane
  assemblies C48·Eₖ (interlocked macrocycles); positive-mode proton adducts
  `[assembly + zH]ᶻ⁺`.
* Quantities: integer atomic masses H = 1, C = 12, N = 14, O = 16
  (source instruction); observed peaks m/z 591, 783, 879, 1174.
* Governing law: with no fragmentation, an assembly's mass is the sum of its
  intact component masses; in positive mode an ion is a proton adduct, so
  m/z = (neutral integer mass + z · 1)/z with charge z ≥ 1.
* Candidate table (marking scheme): the unknown peaks are matched against
  intact ions with exactly one C48 ring, 1–3 macrocycles E, and 1–3 proton
  charges; the table of m/z values is
  C48E: 1167, 584, 389.7 — C48E2: 1757, 879, 586.3 — C48E3: 2347, 1174, 783.
* Given example: m/z 591 ↔ `[E + H]⁺` (free macrocycle, outside the one-C48
  candidate universe).
* Requested conclusions: the identities of the ions at m/z 783, 879 and 1174.

## Assumption / target split

Assumptions (sourced data, carried by definitions): the two molecular
formulas, the integer atomic-mass table, the no-fragmentation sum rule, the
positive-mode proton-adduct model, the four observed m/z values, and the
source's bounded candidate universe (`IsCandidateIon`).
Targets (theorems, proved in a later stage): for each unknown peak, existence
of a candidate ion at that m/z **and** the fact that the m/z equation forces
the reported macrocycle count and proton count — 783 forces (3, 3), 879 forces
(2, 2), 1174 forces (3, 2).  The example `[E + H]⁺` at 591 is checked as
given.  Named-ion m/z equalities are corollaries only; the primary statements
quantify over the bounded candidate universe and never claim uniqueness in
the unrestricted any-count/any-charge space.
-/

namespace IChO2026T6A4

/-! ## Sourced numerical data: integer atomic masses -/

/-- The elements occurring in the species characterised in subquestion 6.4:
carbon (C₄₈ and E), hydrogen, nitrogen and oxygen (E). -/
inductive Element where
  | C
  | H
  | N
  | O

/-- Integer atomic masses, as mandated by the source instruction
"Use integer atomic masses": H = 1, C = 12, N = 14, O = 16. -/
def Element.integerAtomicMass : Element → ℕ
  | .C => 12
  | .H => 1
  | .N => 14
  | .O => 16

/-! ## Molecular formulas and integer molecular masses -/

/-- A molecular formula over the elements C, H, N, O — the only elements
occurring in the two characterised species of this subquestion.  Each field
is the atom count of the corresponding element. -/
structure Formula where
  /-- Atom count of carbon. -/
  C : ℕ
  /-- Atom count of hydrogen. -/
  H : ℕ
  /-- Atom count of nitrogen. -/
  N : ℕ
  /-- Atom count of oxygen. -/
  O : ℕ

/-- The integer molecular mass of a formula: the sum over elements of
(integer atomic mass) × (atom count), per the source's integer-mass
instruction. -/
def Formula.integerMass (f : Formula) : ℕ :=
  Element.integerAtomicMass .C * f.C + Element.integerAtomicMass .H * f.H +
    Element.integerAtomicMass .N * f.N + Element.integerAtomicMass .O * f.O

/-- Macrocycle E, with molecular formula C₄₀H₃₄N₂O₃ as printed beneath its
structure in the source figure (problem PDF page 53, image `T6_page-2.png`). -/
def macrocycleE : Formula := ⟨40, 34, 2, 3⟩

/-- Cyclo[48]carbon, C₄₈: the all-carbon ring stabilised by catenation with
macrocycle E. -/
def cyclo48 : Formula := ⟨48, 0, 0, 0⟩

/-- The molecular weight of macrocycle E is 590, as derived in the marking
scheme from C₄₀H₃₄N₂O₃ with integer atomic masses. -/
theorem macrocycleE_integerMass : macrocycleE.integerMass = 590 := by
  decide

/-- The molecular weight of cyclo[48]carbon C₄₈ is 576, as derived in the
marking scheme. -/
theorem cyclo48_integerMass : cyclo48.integerMass = 576 := by
  decide

/-! ## Catenane assemblies (no fragmentation) -/

/-- A neutral catenane assembly: `cyclo48Count` cyclo[48]carbon rings
interlocked with `macrocycleCount` macrocycles E.  The source assumes no
fragmentation, so the assembly mass is exactly the sum of the intact
component masses; no neutral losses are modelled. -/
structure CatenaneAssembly where
  /-- Number of cyclo[48]carbon rings in the assembly. -/
  cyclo48Count : ℕ
  /-- Number of macrocycles E catenated into the assembly. -/
  macrocycleCount : ℕ

/-- The integer mass of a catenane assembly under the no-fragmentation
assumption: the sum of the intact component molecular masses. -/
def CatenaneAssembly.integerMass (a : CatenaneAssembly) : ℕ :=
  a.cyclo48Count * cyclo48.integerMass + a.macrocycleCount * macrocycleE.integerMass

/-! ## Positive-mode ESI ions and m/z -/

/-- A positive-mode electrospray ion: a neutral assembly carrying
`protonCount` proton adducts, hence charge `protonCount+`.  The proton count
is a positive natural (`ℕ+`) because the spectrum is recorded in positive
mode: every observed ion carries at least one protonic charge.  The type
itself imposes no upper bound on catenation or charge; the source's bounded
candidate universe is the separate predicate `IsCandidateIon`. -/
structure EsiIon where
  /-- The neutral assembly that was protonated. -/
  assembly : CatenaneAssembly
  /-- The number z ≥ 1 of proton adducts, equal to the charge state z+. -/
  protonCount : ℕ+

/-- The integer mass of the ion: the assembly mass plus one mass unit per
attached proton (integer atomic mass of H is 1; the electron mass is
neglected at integer resolution, matching the marking scheme's
`[E + H]⁺ = 590 + 1 = 591`). -/
def EsiIon.integerMass (i : EsiIon) : ℕ :=
  i.assembly.integerMass + (i.protonCount : ℕ) * Element.integerAtomicMass .H

/-- The mass-to-charge ratio m/z of the ion: the integer ion mass divided by
the charge state (the number of proton adducts). -/
noncomputable def EsiIon.mz (i : EsiIon) : ℝ :=
  (i.integerMass : ℝ) / ((i.protonCount : ℕ) : ℝ)

/-! ## The observed spectrum and the source's candidate universe -/

/-- The four intense peaks observed in the positive-mode ESI mass spectrum,
in the source's order: m/z 591, 783, 879, 1174. -/
def observedPeaks : List ℝ := [591, 783, 879, 1174]

/-- The bounded candidate universe of the source's candidate table: an intact
ion containing exactly one cyclo[48]carbon ring, catenated with 1–3
macrocycles E, and carrying 1–3 proton charges.  The given example `[E + H]⁺`
(free macrocycle, no C48 ring) lies outside this universe by design; the
three unknown peaks are identified within it. -/
def IsCandidateIon (i : EsiIon) : Prop :=
  i.assembly.cyclo48Count = 1 ∧
    1 ≤ i.assembly.macrocycleCount ∧ i.assembly.macrocycleCount ≤ 3 ∧
      1 ≤ (i.protonCount : ℕ) ∧ (i.protonCount : ℕ) ≤ 3

/-! ## The given example: m/z 591 -/

/-- `[E + H]⁺`: the free macrocycle E with a single proton adduct — the ion
given in the source as the example assignment for m/z 591. -/
def ion_free_E : EsiIon := ⟨⟨0, 1⟩, 1⟩

/-- The source's given example: the peak at m/z 591 is `[E + H]⁺`. -/
theorem mz_591_example : ion_free_E.mz = 591 := by
  norm_num [ion_free_E, EsiIon.mz, EsiIon.integerMass,
    CatenaneAssembly.integerMass, macrocycleE_integerMass, cyclo48_integerMass,
    Element.integerAtomicMass]

/-! ## Requested conclusions: peak-to-ion identification

For each unknown peak, the primary statement has two parts over the source's
bounded candidate universe: an ion at that m/z **exists**, and any candidate
ion at that m/z is **forced** to have the reported macrocycle count and
proton count.  The answer tuples appear only in these conclusions, never in
a definition or premise used as a witness. -/

/-- The peak at m/z 783 is identified within the candidate universe:
a candidate ion at 783 exists, and the m/z equation forces three macrocycles
and three protons — the ion is `[C48E3 + 3H]³⁺`
((576 + 3 · 590 + 3) / 3 = 2349 / 3 = 783). -/
theorem peak_783_identification :
    (∃ i : EsiIon, IsCandidateIon i ∧ i.mz = 783) ∧
      ∀ i : EsiIon, IsCandidateIon i → i.mz = 783 →
        i.assembly.macrocycleCount = 3 ∧ (i.protonCount : ℕ) = 3 := by
  refine ⟨⟨⟨⟨1, 3⟩, 3⟩, ⟨rfl, by decide, by decide, by decide, by decide⟩, ?_⟩, ?_⟩
  · norm_num [EsiIon.mz, EsiIon.integerMass, CatenaneAssembly.integerMass,
      macrocycleE_integerMass, cyclo48_integerMass, Element.integerAtomicMass]
  · intro i hc hmz
    obtain ⟨⟨c, m⟩, ⟨z, hz⟩⟩ := i
    simp only [IsCandidateIon] at hc
    obtain ⟨hc48, hm1, hm3, hz1, hz3⟩ := hc
    subst hc48
    simp only [EsiIon.mz, EsiIon.integerMass, CatenaneAssembly.integerMass,
      cyclo48_integerMass, macrocycleE_integerMass, Element.integerAtomicMass] at hmz
    rw [div_eq_iff (by exact_mod_cast hz.ne')] at hmz
    have hnat : 1 * 576 + m * 590 + z * 1 = 783 * z := by
      exact_mod_cast hmz
    change m = 3 ∧ z = 3
    exact ⟨by omega, by omega⟩

/-- The peak at m/z 879 is identified within the candidate universe:
a candidate ion at 879 exists, and the m/z equation forces two macrocycles
and two protons — the ion is `[C48E2 + 2H]²⁺`
((576 + 2 · 590 + 2) / 2 = 1758 / 2 = 879). -/
theorem peak_879_identification :
    (∃ i : EsiIon, IsCandidateIon i ∧ i.mz = 879) ∧
      ∀ i : EsiIon, IsCandidateIon i → i.mz = 879 →
        i.assembly.macrocycleCount = 2 ∧ (i.protonCount : ℕ) = 2 := by
  refine ⟨⟨⟨⟨1, 2⟩, 2⟩, ⟨rfl, by decide, by decide, by decide, by decide⟩, ?_⟩, ?_⟩
  · norm_num [EsiIon.mz, EsiIon.integerMass, CatenaneAssembly.integerMass,
      macrocycleE_integerMass, cyclo48_integerMass, Element.integerAtomicMass]
  · intro i hc hmz
    obtain ⟨⟨c, m⟩, ⟨z, hz⟩⟩ := i
    simp only [IsCandidateIon] at hc
    obtain ⟨hc48, hm1, hm3, hz1, hz3⟩ := hc
    subst hc48
    simp only [EsiIon.mz, EsiIon.integerMass, CatenaneAssembly.integerMass,
      cyclo48_integerMass, macrocycleE_integerMass, Element.integerAtomicMass] at hmz
    rw [div_eq_iff (by exact_mod_cast hz.ne')] at hmz
    have hnat : 1 * 576 + m * 590 + z * 1 = 879 * z := by
      exact_mod_cast hmz
    change m = 2 ∧ z = 2
    exact ⟨by omega, by omega⟩

/-- The peak at m/z 1174 is identified within the candidate universe:
a candidate ion at 1174 exists, and the m/z equation forces three
macrocycles and two protons — the ion is `[C48E3 + 2H]²⁺`
((576 + 3 · 590 + 2) / 2 = 2348 / 2 = 1174). -/
theorem peak_1174_identification :
    (∃ i : EsiIon, IsCandidateIon i ∧ i.mz = 1174) ∧
      ∀ i : EsiIon, IsCandidateIon i → i.mz = 1174 →
        i.assembly.macrocycleCount = 3 ∧ (i.protonCount : ℕ) = 2 := by
  refine ⟨⟨⟨⟨1, 3⟩, 2⟩, ⟨rfl, by decide, by decide, by decide, by decide⟩, ?_⟩, ?_⟩
  · norm_num [EsiIon.mz, EsiIon.integerMass, CatenaneAssembly.integerMass,
      macrocycleE_integerMass, cyclo48_integerMass, Element.integerAtomicMass]
  · intro i hc hmz
    obtain ⟨⟨c, m⟩, ⟨z, hz⟩⟩ := i
    simp only [IsCandidateIon] at hc
    obtain ⟨hc48, hm1, hm3, hz1, hz3⟩ := hc
    subst hc48
    simp only [EsiIon.mz, EsiIon.integerMass, CatenaneAssembly.integerMass,
      cyclo48_integerMass, macrocycleE_integerMass, Element.integerAtomicMass] at hmz
    rw [div_eq_iff (by exact_mod_cast hz.ne')] at hmz
    have hnat : 1 * 576 + m * 590 + z * 1 = 1174 * z := by
      exact_mod_cast hmz
    change m = 3 ∧ z = 2
    exact ⟨by omega, by omega⟩

/-! ## Named ions and corollary m/z equalities -/

/-- `[C48E2 + 2H]²⁺`: the di-catenane dication, one cyclo[48]carbon
interlocked with two macrocycles E and doubly protonated. -/
def ion_C48E2_dication : EsiIon := ⟨⟨1, 2⟩, 2⟩

/-- `[C48E3 + 2H]²⁺`: the tri-catenane dication, one cyclo[48]carbon
interlocked with three macrocycles E and doubly protonated. -/
def ion_C48E3_dication : EsiIon := ⟨⟨1, 3⟩, 2⟩

/-- `[C48E3 + 3H]³⁺`: the tri-catenane trication, one cyclo[48]carbon
interlocked with three macrocycles E and triply protonated. -/
def ion_C48E3_trication : EsiIon := ⟨⟨1, 3⟩, 3⟩

/-- Corollary of `peak_783_identification`: the named tri-catenane trication
`[C48E3 + 3H]³⁺` has m/z 783. -/
theorem mz_783 : ion_C48E3_trication.mz = 783 := by
  norm_num [ion_C48E3_trication, EsiIon.mz, EsiIon.integerMass,
    CatenaneAssembly.integerMass, macrocycleE_integerMass, cyclo48_integerMass,
    Element.integerAtomicMass]

/-- Corollary of `peak_879_identification`: the named di-catenane dication
`[C48E2 + 2H]²⁺` has m/z 879. -/
theorem mz_879 : ion_C48E2_dication.mz = 879 := by
  norm_num [ion_C48E2_dication, EsiIon.mz, EsiIon.integerMass,
    CatenaneAssembly.integerMass, macrocycleE_integerMass, cyclo48_integerMass,
    Element.integerAtomicMass]

/-- Corollary of `peak_1174_identification`: the named tri-catenane dication
`[C48E3 + 2H]²⁺` has m/z 1174. -/
theorem mz_1174 : ion_C48E3_dication.mz = 1174 := by
  norm_num [ion_C48E3_dication, EsiIon.mz, EsiIon.integerMass,
    CatenaneAssembly.integerMass, macrocycleE_integerMass, cyclo48_integerMass,
    Element.integerAtomicMass]

end IChO2026T6A4
