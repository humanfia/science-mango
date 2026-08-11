import Mathlib

/-!
# IChO 2026, Theory Problem 1, subquestion 1.6 — the mysterious stone

58th International Chemistry Olympiad (Tashkent, 2026), Problem T1
"A Journey through Time: The Secrets of Avicenna", Part 2, question 1.6
(4.0 pt):

> Determine the chemical formulae of the **stone** and compound **H** using
> thermogravimetric data.

## Source contract

Thermogravimetric analysis of the stone in open air (problem PDF page 9;
page images `T1_page-3.png` and `T1_page-4.png`):

* a 10.00 g sample began to lose mass at approximately 100 °C and the loss
  stopped at 5.75 g at 200 °C (first plateau);
* a second drop in mass was observed at 400 °C, with a final mass of 1.50 g
  of compound H remaining constant at higher temperatures.

Reusable previous-part conclusions (natural-language prerequisites only):

* T1-A4: the metal of the stone is Q = aluminum
  (C·xH₂O = AlF₃·3H₂O, D = Na₃AlF₆);
* T1-A5: the stone contains the anion of the highly symmetrical acid
  F = mellitic acid C₆(COOH)₆, i.e. the mellitate anion C₆(COO)₆⁶⁻ = C₁₂O₁₂⁶⁻.

Hence the stone is a hydrate of the stoichiometric salt aluminum mellitate
Al₂(C₆(COO)₆) (charge neutrality: 2·(+3) + (−6) = 0), and subquestion 1.6
asks for its hydration number `n` and for the chemical formula of the final
residue H. Mass loss starting near 100 °C is the qualitative signature of
water of crystallization (a hydrate); the residue of an air TGA of a metal
carboxylate is the metal oxide.

## Official marking-scheme computation (validation data, not premises)

With atomic masses H = 1.008, C = 12.01, O = 16, Al = 26.98 (g·mol⁻¹),
M(Al₂C₁₂O₁₂) = 26.98·2 + 12.01·12 + 16·12 = 390.08 g·mol⁻¹ and
M(H₂O) = 1.008·2 + 16 = 18.016 g·mol⁻¹:

* Equation (4): 4.25/(18.016·n) = 5.75/390.08, giving n ≈ 16.003,
  hence n = 16 and the stone is Al₂(C₆(COO)₆)·16H₂O (the mineral honeystone);
* Equation (5): 1.50/M = 5.75/390.08, giving M ≈ 101.76 g·mol⁻¹,
  very close to M(Al₂O₃) = 101.96 g·mol⁻¹, hence H = Al₂O₃.

## Modeling notes (assumption/target split)

The theorems below do **not** assume n = 16 or H = Al₂O₃.  They assume:

* the sourced atomic masses, as an explicit hypothesis
  (`AtomicMassTable.IsSourced`);
* the three TGA mass readouts (10.00 g, 5.75 g, 1.50 g);
* the anhydrous composition Al₂C₁₂O₁₂ (reusable conclusion of T1-A4/T1-A5);
* the governing conservation laws in cross-multiplied form with explicit
  tolerances: step 1 is pure dehydration (moles of H₂O released = n × moles
  of anhydrous salt), and step 2 converts one anhydrous formula unit into one
  formula unit of H (aluminum conservation, 2 Al on both sides), with H being
  a binary aluminum oxide Al₂Oₖ.

The tolerances (1 and 2 g²·mol⁻¹) cover the rounding residuals of the
official computation (0.368 and 1.15 in the same cross-multiplied units,
i.e. ≲ 0.4 % relative, consistent with the four-significant-figure data)
while excluding the neighbouring integers by two orders of magnitude, so the
integer unknowns are determined uniquely: n = 16 and k = 3.
-/

namespace IChO2026T1A6

/-- The elements occurring in the mysterious-stone subsystem (T1-A4–T1-A6):
aluminum (metal Q), carbon, hydrogen and oxygen. -/
inductive StoneElement where
  | aluminum
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Repr

/-- An atomic-mass table: the numerical readout of each element's atomic mass
in g·mol⁻¹.  Values enter only through the explicit `IsSourced` hypothesis —
they are sourced data of the official IChO 2026 materials, not axioms. -/
abbrev AtomicMassTable := StoneElement → ℝ

/-- The atomic-mass values used by the official IChO 2026 marking scheme
(g·mol⁻¹): H = 1.008, C = 12.01, O = 16, Al = 26.98. -/
def AtomicMassTable.IsSourced (am : AtomicMassTable) : Prop :=
  am .hydrogen = 1.008 ∧ am .carbon = 12.01
    ∧ am .oxygen = 16 ∧ am .aluminum = 26.98

/-- A chemical formula over the stone elements: the number of atoms of each
element per formula unit.  Species identity is preserved by the fields, so a
conclusion of the form `H = alumina` really identifies the compound. -/
structure Formula where
  /-- aluminum atoms per formula unit -/
  aluminum : ℕ
  /-- carbon atoms per formula unit -/
  carbon : ℕ
  /-- hydrogen atoms per formula unit -/
  hydrogen : ℕ
  /-- oxygen atoms per formula unit -/
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- The molar mass (g·mol⁻¹) of a formula: the atom-count-weighted sum of the
atomic masses. -/
def Formula.molarMass (am : AtomicMassTable) (f : Formula) : ℝ :=
  (f.aluminum : ℝ) * am .aluminum + (f.carbon : ℝ) * am .carbon
    + (f.hydrogen : ℝ) * am .hydrogen + (f.oxygen : ℝ) * am .oxygen

/-- Water, H₂O — the water of crystallization released in the first TGA step
(mass loss from ≈100 °C, complete by 200 °C). -/
def water : Formula := ⟨0, 0, 2, 1⟩

/-- Anhydrous aluminum mellitate, Al₂(C₆(COO)₆) = Al₂C₁₂O₁₂: two Al³⁺ cations
per mellitate anion C₆(COO)₆⁶⁻.  This is the reusable conclusion of T1-A4
(metal Q = Al) and T1-A5 (acid F = mellitic acid C₆(COOH)₆; the stone
contains its anion). -/
def aluminumMellitate : Formula := ⟨2, 12, 0, 12⟩

/-- Aluminum oxide (alumina), Al₂O₃ — the candidate identity of the final TGA
residue H.  Nothing in the hypotheses below assumes H equals this formula;
the theorems derive it. -/
def alumina : Formula := ⟨2, 0, 0, 3⟩

/-- A hydrated stoichiometric compound: an anhydrous formula together with
its number of waters of crystallization.  Keeping the hydrate structure
(rather than a collapsed overall formula) preserves the chemical meaning of
the first TGA step. -/
structure Hydrate where
  /-- the anhydrous formula -/
  anhydrous : Formula
  /-- waters of crystallization per anhydrous formula unit -/
  waters : ℕ
  deriving DecidableEq, Repr

/-- The molar mass (g·mol⁻¹) of a hydrate: the anhydrous molar mass plus the
waters of crystallization. -/
def Hydrate.molarMass (am : AtomicMassTable) (s : Hydrate) : ℝ :=
  Formula.molarMass am s.anhydrous + (s.waters : ℝ) * Formula.molarMass am water

/-- The thermogravimetric readout for the stone (all masses in g).
Qualitative temperature context from the source: mass loss began at
approximately 100 °C, the first plateau held at 200 °C, the second mass drop
occurred at 400 °C, and the residue mass stayed constant at higher
temperatures. -/
structure ThermogravimetryData where
  /-- initial sample mass (10.00 g) -/
  initialMass : ℝ
  /-- first-plateau mass at 200 °C: the anhydrous salt (5.75 g) -/
  plateauMass : ℝ
  /-- final residue mass: compound H (1.50 g) -/
  residueMass : ℝ

/-- **Subquestion 1.6, first output: the chemical formula of the stone.**

If `stone` is a hydrate of anhydrous aluminum mellitate (T1-A4/T1-A5 reusable
conclusions) whose dehydration obeys the step-1 mass balance
`(m₀ − m₁)·M(anhydrous) = n·M(H₂O)·m₁` up to the data-rounding tolerance
(given masses m₀ = 10.00 g, m₁ = 5.75 g, molar masses from the sourced atomic
mass table), then the stone is Al₂(C₆(COO)₆)·16H₂O.

This is the cross-multiplied form of the marking scheme's Equation (4),
`4.25/(18.016·n) = 5.75/390.08`; the tolerance 1 (g²·mol⁻¹) covers the
official computation's residual 0.368 while forcing the natural number
`stone.waters` into [15.99, 16.02], i.e. `stone.waters = 16`. -/
theorem stone_formula
    (am : AtomicMassTable) (ham : am.IsSourced)
    (tga : ThermogravimetryData)
    (hm0 : tga.initialMass = 10.00) (hm1 : tga.plateauMass = 5.75)
    (stone : Hydrate)
    (hanh : stone.anhydrous = aluminumMellitate)
    (hstep : |(tga.initialMass - tga.plateauMass)
                * Formula.molarMass am stone.anhydrous
              - (stone.waters : ℝ) * Formula.molarMass am water
                * tga.plateauMass| ≤ 1) :
    stone = ⟨aluminumMellitate, 16⟩ := by
  obtain ⟨hamH, hamC, hamO, hamAl⟩ := ham
  -- M(Al₂C₁₂O₁₂) = 2·26.98 + 12·12.01 + 12·16 = 390.08 g·mol⁻¹
  have hM_anh : Formula.molarMass am aluminumMellitate = 390.08 := by
    norm_num [Formula.molarMass, aluminumMellitate, hamH, hamC, hamO, hamAl]
  -- M(H₂O) = 2·1.008 + 16 = 18.016 g·mol⁻¹
  have hM_wat : Formula.molarMass am water = 18.016 := by
    norm_num [Formula.molarMass, water, hamH, hamC, hamO, hamAl]
  -- Step-1 balance with w := stone.waters: |1657.84 − 103.592·w| ≤ 1
  rw [hm0, hm1, hanh, hM_anh, hM_wat, abs_le] at hstep
  -- hence 15.993… ≤ w ≤ 16.013…
  have h15 : (15 : ℝ) < stone.waters := by linarith [hstep.2]
  have h17 : (stone.waters : ℝ) < 17 := by linarith [hstep.1]
  have hw : stone.waters = 16 := by
    have h15' : 15 < stone.waters := by exact_mod_cast h15
    have h17' : stone.waters < 17 := by exact_mod_cast h17
    omega
  -- stone = ⟨stone.anhydrous, stone.waters⟩ = ⟨aluminumMellitate, 16⟩
  change ({ anhydrous := stone.anhydrous, waters := stone.waters } : Hydrate)
    = ⟨aluminumMellitate, 16⟩
  rw [Hydrate.mk.injEq]
  exact ⟨hanh, hw⟩

/-- **Subquestion 1.6, second output: the chemical formula of compound H.**

If H is a binary aluminum oxide with two aluminum atoms per formula unit
(the air-TGA residue of an aluminum carboxylate is the metal oxide, and
aluminum conservation with the 1:1 formula-unit stoichiometry of step 2 gives
2 Al per formula unit) whose formation obeys the step-2 mass balance
`M(H)·m₁ = m₂·M(anhydrous)` up to the data-rounding tolerance (given masses
m₁ = 5.75 g, m₂ = 1.50 g, molar masses from the sourced atomic mass table),
then H is Al₂O₃.

This is the cross-multiplied form of the marking scheme's Equation (5),
`1.50/M = 5.75/390.08` (M ≈ 101.76 g·mol⁻¹): writing H = Al₂Oₖ, the balance
reads |310.27 + 92·k − 585.12| ≤ 2, forcing the natural number k into
[2.96, 3.01], i.e. k = 3 — matching M(Al₂O₃) = 101.96 g·mol⁻¹ within
0.2 g·mol⁻¹, the marking scheme's "very close". -/
theorem residue_formula
    (am : AtomicMassTable) (ham : am.IsSourced)
    (tga : ThermogravimetryData)
    (hm1 : tga.plateauMass = 5.75) (hm2 : tga.residueMass = 1.50)
    (H : Formula) (k : ℕ)
    (hH_al : H.aluminum = 2) (hH_c : H.carbon = 0)
    (hH_h : H.hydrogen = 0) (hH_o : H.oxygen = k)
    (hstep : |Formula.molarMass am H * tga.plateauMass
              - tga.residueMass * Formula.molarMass am aluminumMellitate| ≤ 2) :
    H = alumina := by
  obtain ⟨hamH, hamC, hamO, hamAl⟩ := ham
  -- M(Al₂C₁₂O₁₂) = 390.08 g·mol⁻¹, as in `stone_formula`
  have hM_anh : Formula.molarMass am aluminumMellitate = 390.08 := by
    norm_num [Formula.molarMass, aluminumMellitate, hamH, hamC, hamO, hamAl]
  -- For H = Al₂Oₖ: M(H) = 2·26.98 + 16·k = 53.96 + 16·k
  have hM_H : Formula.molarMass am H = 53.96 + 16 * (k : ℝ) := by
    simp only [Formula.molarMass, hH_al, hH_c, hH_h, hH_o, hamH, hamC, hamO, hamAl]
    norm_num
    ring
  -- Step-2 balance: |310.27 + 92·k − 585.12| ≤ 2
  rw [hm1, hm2, hM_anh, hM_H, abs_le] at hstep
  -- hence 2.965… ≤ k ≤ 3.009…
  have h2 : (2 : ℝ) < k := by linarith [hstep.1]
  have h4 : (k : ℝ) < 4 := by linarith [hstep.2]
  have hk : k = 3 := by
    have h2' : 2 < k := by exact_mod_cast h2
    have h4' : k < 4 := by exact_mod_cast h4
    omega
  -- H = ⟨2, 0, 0, k⟩ = ⟨2, 0, 0, 3⟩ = alumina
  change ({ aluminum := H.aluminum, carbon := H.carbon, hydrogen := H.hydrogen,
            oxygen := H.oxygen } : Formula) = ⟨2, 0, 0, 3⟩
  rw [Formula.mk.injEq]
  exact ⟨hH_al, hH_c, hH_h, by rw [hH_o, hk]⟩

end IChO2026T1A6
