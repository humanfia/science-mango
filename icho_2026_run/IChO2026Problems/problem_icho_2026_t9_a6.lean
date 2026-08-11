import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 · Problem T9 (Cyclodextrin Chemistry) · Subquestion 9.6

**Source.** 58th International Chemistry Olympiad, Tashkent 2026, theory exam,
problem T9, printed page Q9-3 (image evidence: `T9_page-3.png`; scheme context
on `T9_page-2.png`).

**Question 9.6 (4.0 pt).** *Determine the number of isomers of the β-CD dimer that
can form during the synthesis by Sinay et al.*

## The chemistry being modelled

β-Cyclodextrin (β-CD) is a cyclic oligosaccharide of **seven** α-D-glucopyranoside
units joined by α-1,4-glycosidic bonds (problem introduction). The Sinay dimer
synthesis drawn above questions 9.5/9.6 runs:

1. `NaH (30 equiv.), BnCl (30 equiv.)` — perbenzylation of all 21 hydroxy groups
   of β-CD (7 primary `CH₂OH` + 14 secondary `(OH)₁₄`);
2. `DIBAL–H (2 equiv.)` — regioselective reductive debenzylation giving **L**.
   Per the problem text: *a single protic group (NH and OH) at unit 1 directs the
   next reductive debenzylation of a primary OH group to unit 4 in the macrocyclic
   ring (or to unit 3 if the unit 4 position is not available)*. Hence L carries
   exactly two free primary OH groups, on unit 1 and on unit 4 (ring offset `+3`);
3. `t-BuOK`, ω-bromoalkene — Williamson alkylation of **one** of the two free OH
   groups of L, installing the terminal-alkene linker precursor. Both free OH
   groups are primary 6-OH groups and react, so two regioisomeric monomers arise —
   `M-1R` (alkenyl on unit 1) and `M-4R` (alkenyl on unit 4). They are distinct
   because the ring has *seven* units and is *chiral*: no rotation of the ring
   exchanges them (offset `+3 ≢ −3 mod 7`), and chirality forbids identification
   by reflection;
4. `Grubbs I` — terminal-alkene metathesis joining two monomers through their
   alkenyl chains (homo- and cross-pairing both occur);
5. `H₂, PtO₂` — hydrogenation of the resulting internal alkene, so the final
   linker is a constitutionally symmetric, stereochemically inert alkylene bridge.
   Consequently a dimer is an **unordered** pair of monomer regioisomers — the
   official rubric's "(Note 4-1 = 1-4)".

The dimer drawn in the exam (per ring: 5 × `CH₂OBn`, 1 × free `CH₂OH`,
1 × `CH₂O–linker`, and `(OBn)₁₄` on the secondary face) confirms this reading.

## Assumption / target split

*Assumptions* (carried by the definitions below, each traced to the problem text
or scheme): the ring size 7 (`betaCDNumUnits`, `UnitPos`); chirality as
identification of substitution patterns up to rotation only (`RotationEquiv`);
the Sinay directing rule with both of its branches (`sinayOffset`); the
two-free-OH structure of L (`IsLPattern`); single-site alkylation of either free
OH (`IsAlkylatedMonomer`); free pairwise metathesis with a symmetric
stereochemically inert linker (`DimerIsomer := Sym2 MonomerIsomer`). The 14
secondary benzyl ethers are constant through the whole sequence and are therefore
not tracked (they cannot distinguish isomers).

*Targets* (the requested outputs, to be proved in the prover stage): exactly two
monomer regioisomers exist (`monomer_regioisomers_card`, with
`M1R_ne_M4R` isolating the "seven units and chiral" step); every dimer is one of
the 4-4, 1-1 and 1-4 connections (`dimer_isomers_enumeration`); the three
connections are pairwise distinct (`dimer_isomers_distinct`); and the final
count **3** (`icho_2026_t9_a6_number_of_dimer_isomers`).

The recorded answer is *not* used as a premise: the count emerges from the ring
model (`ZMod 7`, rotations only, Sinay offset `+3`) by finite enumeration.
-/

namespace IChO2026.T9.A6

/-! ## Shared problem data: the β-cyclodextrin ring -/

/-- Number of α-D-glucopyranoside units in β-cyclodextrin: **7**
(problem introduction: α-, β- and γ-CD contain 6, 7 and 8 units respectively). -/
def betaCDNumUnits : ℕ := 7

theorem betaCDNumUnits_eq : betaCDNumUnits = 7 := rfl

/-- The glucopyranose units of β-CD, indexed by `ZMod 7` (i.e. `ZMod betaCDNumUnits`).
The `ZMod 7` addition encodes the oriented α-1,4-glycosidic ring direction:
"unit 4 relative to unit 1" is the position at offset `+3`. -/
abbrev UnitPos := ZMod 7

/-! ## Primary-face substitution patterns -/

/-- State of the primary (C6) position of one glucopyranose unit along the Sinay
β-CD-dimer synthesis:

* `OBn` — benzyl-protected primary hydroxy (installed by the `NaH`/`BnCl`
  perbenzylation);
* `OH` — free primary hydroxy, the protic group of the Sinay directing effect
  (revealed by `DIBAL–H` reductive debenzylation);
* `alkenyl` — the ω-alkenyl ether installed by `t-BuOK` / ω-bromoalkene; this is
  the precursor of the inter-CD linker formed by Grubbs-I metathesis and
  `H₂`/`PtO₂` hydrogenation. -/
inductive PrimarySubstituent
  | OBn
  | OH
  | alkenyl
  deriving DecidableEq

/-- A primary-face substitution pattern: the substituent at the C6 position of each
of the seven units. The 14 secondary (C2/C3) positions remain benzyl-protected
throughout the whole sequence (the `(OBn)₁₄` label of the scheme) and are not
tracked: they are identical in every intermediate and product and therefore cannot
distinguish isomers. -/
abbrev Pattern := UnitPos → PrimarySubstituent

/-- **Chirality of β-CD.** Two substitution patterns describe the same cyclodextrin
derivative iff they differ by a *rotation* of the macrocycle. Identification by a
reflection is excluded: all seven glucose units are D-configured, so a mirror-image
pattern is a different molecule, not the same one. This is the formal content of
"β-CD … being chiral" in the official answer. -/
def RotationEquiv (f g : Pattern) : Prop := ∃ c : UnitPos, ∀ i, f i = g (i + c)

/-- Rotational identification of patterns is an equivalence relation. -/
theorem rotationEquiv_equivalence : Equivalence RotationEquiv := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact ⟨0, fun i => by rw [add_zero]⟩
  · rintro f g ⟨c, h⟩
    refine ⟨-c, fun i => ?_⟩
    have h' := h (i + -c)
    rw [show i + -c + c = i by abel] at h'
    exact h'.symm
  · rintro f g h ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    exact ⟨c₁ + c₂, fun i => by rw [h₁ i, h₂ (i + c₁), add_assoc]⟩

/-! ## The Sinay directing rule and the intermediate L -/

/-- **Sinay's directing rule** (problem text, T9 page 3): a single protic group
(NH or OH) on unit 1 directs the *next* reductive debenzylation of a primary benzyl
ether to unit 4 of the macrocyclic ring — i.e. to ring offset `+3` — or to unit 3
(offset `+2`) if the unit-4 position is not available, i.e. for rings of fewer than
four units. Both branches of the rule are kept; for β-CD the first branch applies. -/
def sinayOffset (ringSize : ℕ) : ℕ := if 4 ≤ ringSize then 3 else 2

/-- For β-CD (7 units) the unit-4 position exists, so the Sinay offset is `+3`. -/
theorem sinayOffset_betaCD : sinayOffset betaCDNumUnits = 3 := by decide

/-- The intermediate **L** of question 9.5: perbenzylated β-CD after the two
`DIBAL–H` debenzylations. The first debenzylation reveals a free primary OH (the
directing protic group, conventionally unit 1); the second — the "next"
debenzylation of the Sinay rule — is directed to the unit at the Sinay offset from
it (unit 4 for β-CD). Every other primary position remains a benzyl ether. -/
def IsLPattern (l : Pattern) : Prop :=
  ∃ i : UnitPos,
    l i = .OH ∧
    l (i + (sinayOffset betaCDNumUnits : UnitPos)) = .OH ∧
    ∀ j : UnitPos, j ≠ i → j ≠ i + (sinayOffset betaCDNumUnits : UnitPos) → l j = .OBn

/-- An alkylated monomer of step 3 (`t-BuOK`, ω-bromoalkene): obtained from some L
by converting **one** of its free primary OH groups into the ω-alkenyl ether and
leaving every other unit untouched. Both free OH groups of L are primary 6-OH
groups of comparable reactivity, so both choices occur — this branch point is what
question 9.6 asks to count. -/
def IsAlkylatedMonomer (m : Pattern) : Prop :=
  ∃ l : Pattern, IsLPattern l ∧ ∃ a : UnitPos,
    l a = .OH ∧ m a = .alkenyl ∧ ∀ j : UnitPos, j ≠ a → m j = l j

/-! ## Monomer regioisomers -/

/-- A monomer pattern together with its synthesis-validity certificate. -/
abbrev AlkylatedMonomer := { m : Pattern // IsAlkylatedMonomer m }

/-- Monomers are identified up to macrocycle rotation (chirality: no reflection). -/
instance setoidAlkylatedMonomer : Setoid AlkylatedMonomer where
  r m₁ m₂ := RotationEquiv m₁.1 m₂.1
  iseqv :=
    { refl := fun m => rotationEquiv_equivalence.refl m.1
      symm := fun h => rotationEquiv_equivalence.symm h
      trans := fun h₁ h₂ => rotationEquiv_equivalence.trans h₁ h₂ }

/-- The type of monomer regioisomers: rotation classes of valid alkylated-monomer
patterns. -/
abbrev MonomerIsomer := Quotient setoidAlkylatedMonomer

/-- The canonical L: free primary OH on unit 1 (position `0`, the directing unit)
and on unit 4 (position `3 = 0 +` Sinay offset); benzyl ethers elsewhere. Any valid
L is a rotation of this one, because an L-pattern is determined by its OH pair
`{i, i + 3}`. -/
def patternL : Pattern := fun i => if i = 0 ∨ i = 3 then .OH else .OBn

/-- `patternL` satisfies the L-specification: directing unit `0`, second free OH at
offset `+3`, benzyl ethers at the remaining five positions. -/
theorem isLPattern_patternL : IsLPattern patternL := by
  exact ⟨0, by decide, by decide, by decide⟩

/-- **M-1R pattern**: the ω-alkenyl linker precursor sits on the directing unit 1
itself; unit 4 retains the free OH. -/
def patternM1R : Pattern :=
  fun i => if i = 0 then .alkenyl else if i = 3 then .OH else .OBn

/-- **M-4R pattern**: the ω-alkenyl linker precursor sits on unit 4 (the
Sinay-directed position); unit 1 retains the free OH. -/
def patternM4R : Pattern :=
  fun i => if i = 0 then .OH else if i = 3 then .alkenyl else .OBn

/-- `M-1R` arises by alkylating `patternL` at its unit-1 OH. -/
theorem isAlkylatedMonomer_patternM1R : IsAlkylatedMonomer patternM1R := by
  exact ⟨patternL, isLPattern_patternL, 0, by decide, by decide, by decide⟩

/-- `M-4R` arises by alkylating `patternL` at its unit-4 OH. -/
theorem isAlkylatedMonomer_patternM4R : IsAlkylatedMonomer patternM4R := by
  exact ⟨patternL, isLPattern_patternL, 3, by decide, by decide, by decide⟩

/-- The monomer regioisomer with the linker precursor on unit 1 (rubric's `M-1R`). -/
def M1R : MonomerIsomer := ⟦⟨patternM1R, isAlkylatedMonomer_patternM1R⟩⟧

/-- The monomer regioisomer with the linker precursor on unit 4 (rubric's `M-4R`). -/
def M4R : MonomerIsomer := ⟦⟨patternM4R, isAlkylatedMonomer_patternM4R⟩⟧

/-- **Chirality at work.** The two monomer regioisomers are genuinely different: a
rotation identifying `M-1R` with `M-4R` would have to send the alkenyl position `0`
to `3`, i.e. be the shift by `+3`, but that shift sends the free-OH position `3` to
`6 ≠ 0` — equivalently `+3 ≢ −3 (mod 7)`. This is precisely where "β-CD consists of
seven units and is chiral" enters the official answer. (Proof route: unfold the
quotient equality to `RotationEquiv`, match the unique alkenyl position to force
`c = 3`, then read off the OH positions.) -/
theorem M1R_ne_M4R : M1R ≠ M4R := by
  intro h
  have hr : ∃ c : UnitPos, ∀ i, patternM1R i = patternM4R (i + c) := Quotient.exact h
  exact absurd hr (by decide)

/-- Every alkylated monomer is one of the two regioisomers: an L-pattern is
determined up to rotation by its OH pair `{i, i + 3}`, and the alkylation chooses
one of the two free OH groups. -/
theorem monomer_isomers_enumeration : ∀ m : MonomerIsomer, m = M1R ∨ m = M4R := by
  intro m
  obtain ⟨p, rfl⟩ := Quotient.exists_rep m
  obtain ⟨pat, hpat⟩ := p
  obtain ⟨l, hl, a, hla, hma, hmj⟩ := hpat
  obtain ⟨i, hi1, hi2, hj⟩ := hl
  have hoff : (sinayOffset betaCDNumUnits : UnitPos) = 3 := by
    rw [sinayOffset_betaCD]
    norm_num
  rw [hoff] at hi2 hj
  -- the alkylated site `a` carries a free OH in `l`, so it is one of the two OH positions
  have ha : i = a ∨ a = i + 3 := by
    by_contra h
    push Not at h
    have hObn := hj a h.1.symm h.2
    rw [hla] at hObn
    exact PrimarySubstituent.noConfusion hObn
  -- the two OH positions are distinct (offset `+3 ≢ 0 mod 7`)
  have hne : (i : UnitPos) + 3 ≠ i := by
    intro h
    have h3 : (3 : UnitPos) = 0 := by linear_combination h
    exact absurd h3 (by decide)
  have hne' : (i : UnitPos) ≠ i + 3 := hne.symm
  rcases ha with rfl | rfl
  · -- alkylation at the directing unit: the monomer `M-1R`
    left
    apply Quotient.sound
    change RotationEquiv pat patternM1R
    refine ⟨-i, fun j => ?_⟩
    have hpat4 : pat (i + 3) = .OH := by rw [hmj (i + 3) hne, hi2]
    by_cases h1 : j = i
    · subst h1
      rw [show j + -j = (0 : UnitPos) from add_neg_cancel j, hma]
      rfl
    · by_cases h2 : j = i + 3
      · subst h2
        rw [show i + 3 + -i = (3 : UnitPos) by ring, hpat4]
        rfl
      · have hpat : pat j = .OBn := by rw [hmj j h1, hj j h1 h2]
        rw [hpat]
        have h3 : j + -i ≠ (0 : UnitPos) := by
          intro h; exact h1 (by linear_combination h)
        have h4 : j + -i ≠ (3 : UnitPos) := by
          intro h; exact h2 (by linear_combination h)
        simp [patternM1R, h3, h4]
  · -- alkylation at the Sinay-directed unit: the monomer `M-4R`
    right
    apply Quotient.sound
    change RotationEquiv pat patternM4R
    refine ⟨-i, fun j => ?_⟩
    have hpat1 : pat i = .OH := by rw [hmj i hne', hi1]
    by_cases h1 : j = i
    · subst h1
      rw [show j + -j = (0 : UnitPos) from add_neg_cancel j, hpat1]
      rfl
    · by_cases h2 : j = i + 3
      · subst h2
        rw [show i + 3 + -i = (3 : UnitPos) by ring, hma]
        rfl
      · have hpat : pat j = .OBn := by rw [hmj j h2, hj j h1 h2]
        rw [hpat]
        have h3 : j + -i ≠ (0 : UnitPos) := by
          intro h; exact h1 (by linear_combination h)
        have h4 : j + -i ≠ (3 : UnitPos) := by
          intro h; exact h2 (by linear_combination h)
        simp [patternM4R, h3, h4]

/-- The official answer's first clause: **two** regioisomers are formed in the
alkylation reaction (`M-4R`, `M-1R`). -/
theorem monomer_regioisomers_card : Nat.card MonomerIsomer = 2 := by
  have hbij : Function.Bijective
      (fun b : Bool => match b with | true => M1R | false => M4R) := by
    constructor
    · intro b₁ b₂ h
      cases b₁ <;> cases b₂
      · rfl
      · exact absurd h.symm M1R_ne_M4R
      · exact absurd h M1R_ne_M4R
      · rfl
    · intro m
      rcases monomer_isomers_enumeration m with h | h
      · exact ⟨true, by rw [h]⟩
      · exact ⟨false, by rw [h]⟩
  have hcard := Nat.card_eq_of_bijective _ hbij
  rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_bool]

/-! ## The dimer and the isomer count -/

/-- **The β-CD dimer space.** Steps 4–5 (Grubbs-I metathesis, then `H₂`/`PtO₂`)
join two monomers through their terminal alkenes. Any two monomers can pair
(homo- and cross-metathesis both occur), and the hydrogenated linker is
constitutionally symmetric and bears no stereogenic element (the E/Z isomerism of
the metathesis intermediate is removed by hydrogenation), so a dimer is exactly an
*unordered* pair of monomer regioisomers — `Sym2 MonomerIsomer`, diagonal included
(the 1-1 and 4-4 homodimers). This is the rubric's "(Note 4-1 = 1-4)". -/
abbrev DimerIsomer := Sym2 MonomerIsomer

/-- The three rubric dimers: the 4-4, 1-1 and 1-4 connections. Every dimer is one
of them, because every monomer is `M-1R` or `M-4R` and pairing is unordered. -/
theorem dimer_isomers_enumeration :
    ∀ d : DimerIsomer, d = s(M4R, M4R) ∨ d = s(M1R, M1R) ∨ d = s(M1R, M4R) := by
  intro d
  induction d using Sym2.ind with
  | h x y =>
    rcases monomer_isomers_enumeration x with hx | hx <;>
      rcases monomer_isomers_enumeration y with hy | hy <;> subst hx <;> subst hy
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inr Sym2.eq_swap)
    · exact Or.inl rfl

/-- The three connections are pairwise distinct constitutional isomers. -/
theorem dimer_isomers_distinct :
    s(M4R, M4R) ≠ s(M1R, M1R) ∧ s(M4R, M4R) ≠ s(M1R, M4R) ∧ s(M1R, M1R) ≠ s(M1R, M4R) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [Sym2.eq_iff] at h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    first
      | exact M1R_ne_M4R h1
      | exact M1R_ne_M4R h1.symm
      | exact M1R_ne_M4R h2
      | exact M1R_ne_M4R h2.symm

/-- **IChO 2026 T9.6 (4.0 pt) — final target.** The number of constitutional
(linkage) isomers of the β-CD dimer that can form during the synthesis by
Sinay et al. is **3**: the 4-4, 1-1 and 1-4 connected dimers. -/
theorem icho_2026_t9_a6_number_of_dimer_isomers : Nat.card DimerIsomer = 3 := by
  have hbij : Function.Bijective
      (fun k : Fin 3 =>
        if k = 0 then s(M4R, M4R) else if k = 1 then s(M1R, M1R) else s(M1R, M4R)) := by
    constructor
    · intro k₁ k₂ h
      fin_cases k₁ <;> fin_cases k₂ <;>
        first
          | rfl
          | exact absurd h dimer_isomers_distinct.1
          | exact absurd h dimer_isomers_distinct.2.1
          | exact absurd h dimer_isomers_distinct.2.2
          | exact absurd h.symm dimer_isomers_distinct.1
          | exact absurd h.symm dimer_isomers_distinct.2.1
          | exact absurd h.symm dimer_isomers_distinct.2.2
    · intro d
      rcases dimer_isomers_enumeration d with h | h | h
      · exact ⟨0, rfl.trans h.symm⟩
      · exact ⟨1, rfl.trans h.symm⟩
      · exact ⟨2, rfl.trans h.symm⟩
  have hcard := Nat.card_eq_of_bijective _ hbij
  rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_fin]

end IChO2026.T9.A6
