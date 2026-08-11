import Mathlib
import IChO2026Chem.Core

/-!
# IChO 2026, Theory Problem T5 (Cardiolipins) — Subquestion 5.3

## Source contract (58th IChO, Tashkent 2026; T5.3, 4 pt)

> **Determine** the molecular formula of the fatty acid (RCOOH), if the
> non-ionised form of **PL1** contains 255 σ and π bonds between atoms in
> total. **Support** your answer with calculations. If you were unable to find
> the structural formula of PL1, you can use a–d fragments from 5.1.

Structural context carried from the problem statement (official English
pages Q5-1 and Q5-3):

* PL1 is a cardiolipin assembled exclusively from fragments **a–d** in the
  quantities `a × n`, `b × 2`, `c × 3`, `d × 4`; every open (“wavy”) valence
  of a fragment is paired with exactly one other open valence to form a bond.
  PL1 contains no peroxide bonds and is acyclic.
  - **a** is `~–H` — one open valence, no internal bonds;
  - **b** is a phosphoric-acid residue `~P(=O)(–OH)~` — internal bonds
    P=O (one σ + one π), P–OH and O–H; two open valences;
  - **c** is a glyceryl residue `~O–CH2–CH(O~)–CH2–O~` — internal bonds
    3 C–O, 2 C–C and 5 C–H; three open valences;
  - **d** is an acyl residue `~–C(=O)–R` — internal bonds C=O (one σ + one π)
    and C(=O)–R; one open valence. Here `R = C_xH_y` is an acyclic
    hydrocarbon substituent, identical in all four fatty acid residues.
* Reusable previous-part conclusion (natural-language prerequisite only,
  from 5.2): the number of **a** fragments in PL1 is `n = 1`.
* During reductive ozonolysis, RCOOH forms **three different organic
  products in equimolar amounts**.

## Assumption / target split

Hypotheses of the theorems below:

1. `h_unsat` — R is an acyclic monovalent hydrocarbon group `C_xH_y` whose
   only unsaturation is `d` C=C double bonds; the saturated acyclic
   substituent would be `C_xH_{2x+1}` and each C=C removes two hydrogens,
   hence `y + 2·d = 2·x + 1`.
2. `h_ozone` — reductive ozonolysis cleaves every C=C bond once, so an
   acyclic fatty acid with `d` C=C bonds affords `d + 1` carbonyl products,
   one molecule of each per molecule of acid (hence automatically
   equimolar); the observed three different products force `d + 1 = 3`.
3. `h_bonds` — the non-ionised PL1 assembled from 1×a, 2×b, 3×c, 4×d
   contains 255 σ-and-π bonds in total, where each fragment contributes its
   internal bonds plus ½ per open valence (the two halves of every
   inter-fragment bond are then counted once in total).

Target: `x = 17` and `y = 31`, i.e. the fatty acid is `C17H31–COOH`,
molecular formula **C18H32O2**.

The recorded answer is used only for validation (see the `example`s at the
bottom); no hypothesis, definition, or structure field contains `x = 17`,
`y = 31`, `d = 2`, or the formula `C18H32O2`.
-/

namespace IChO2026T5A3

/-- A molecular formula over the elements carbon, hydrogen and oxygen —
the only elements occurring in the fatty acid RCOOH of this problem. -/
structure MolecularFormula where
  /-- Number of carbon atoms. -/
  C : ℕ
  /-- Number of hydrogen atoms. -/
  H : ℕ
  /-- Number of oxygen atoms. -/
  O : ℕ
deriving Repr, DecidableEq

/-- The fatty acid `R–COOH` with hydrocarbon substituent `R = C_xH_y`:
the carboxyl group contributes one further carbon, one further hydrogen
(the acidic O–H), and two oxygens. -/
def rcoohFormula (x y : ℕ) : MolecularFormula := ⟨x + 1, y + 1, 2⟩

/-!
### Fragment multiplicities in PL1

The quantities `2 × b`, `3 × c`, `4 × d` are stated on problem page Q5-1;
`1 × a` (i.e. `n = 1`) is the reusable conclusion of subquestion 5.2,
taken here as a natural-language prerequisite.
-/

/-- Number of type **a** fragments (`~–H`) in one molecule of PL1: `n = 1`. -/
def pl1FragCountA : ℕ := 1

/-- Number of type **b** fragments (phosphoric-acid residue) in PL1. -/
def pl1FragCountB : ℕ := 2

/-- Number of type **c** fragments (glyceryl residue) in PL1. -/
def pl1FragCountC : ℕ := 3

/-- Number of type **d** fragments (acyl residue `~–C(=O)–R`) in PL1. -/
def pl1FragCountD : ℕ := 4

/-!
### σ+π bond counts of the fragments

Bonds are counted as σ + π (a double bond contributes 2), and every open
(“wavy”) valence contributes ½, so that when two fragments are joined the
two halves together count the newly formed bond exactly once.
-/

/-- Fragment **a**, `~–H`: no internal bonds and one open valence,
contributing `½`. -/
def fragABonds : ℚ := 1 / 2

/-- Fragment **b**, `~P(=O)(–OH)~`: the internal bonds P=O (σ + π, i.e. 2),
P–OH (1) and O–H (1), plus two open valences (`2 × ½`). Total `5`. -/
def fragBBonds : ℚ := 2 + 1 + 1 + 2 * (1 / 2)

/-- Fragment **c**, `~O–CH2–CH(O~)–CH2–O~` (glyceryl): the internal bonds
3 C–O, 2 C–C and 5 C–H (i.e. 10), plus three open valences (`3 × ½`).
Total `23/2`. -/
def fragCBonds : ℚ := 10 + 3 * (1 / 2)

/-- Fragment **d**, `~–C(=O)–R` with `R = C_xH_y` an acyclic monovalent
hydrocarbon substituent: the internal bonds C=O (σ + π, i.e. 2) and
C(=O)–R (1), plus the bonds inside R, plus one open valence (`½`).

The bond count inside R follows from the valence sum: the atoms of
`C_xH_y` carry `4x + y` valences in total (carbon tetravalent, hydrogen
monovalent); one valence is the free valence tying R to the carbonyl
carbon, and every internal bond consumes two valences, so R contains
`(4x + y − 1)/2` σ+π bonds. -/
def fragDBonds (x y : ℕ) : ℚ := 2 + 1 + (4 * (x : ℚ) + (y : ℚ) - 1) / 2 + 1 / 2

/-- Total number of σ-and-π bonds in the non-ionised form of PL1 assembled
from 1×a, 2×b, 3×c and 4×d, as a function of the substituent `R = C_xH_y`.

This is the fragment bond-sum sanctioned by the problem itself (“you can
use a–d fragments from 5.1”): each fragment contributes its internal bonds
plus ½ per open valence. -/
def pl1TotalBonds (x y : ℕ) : ℚ :=
  (pl1FragCountA : ℚ) * fragABonds + (pl1FragCountB : ℚ) * fragBBonds +
    (pl1FragCountC : ℚ) * fragCBonds + (pl1FragCountD : ℚ) * fragDBonds x y

/-- Number of organic products of the reductive ozonolysis of an acyclic
fatty acid `R–COOH` containing `d` C=C double bonds: ozonolysis cleaves
each C=C bond once, splitting the chain into `d + 1` carbonyl fragments,
each of which gives one product molecule per molecule of acid (so the
products are formed in equimolar amounts). -/
def ozonolysisProductCount (d : ℕ) : ℕ := d + 1

/-!
### The three rubric steps of the official marking scheme

The marking scheme awards: 1 pt for the number of double bonds, 2 pt for
the bond-count equation `4x + y = 99` (eq. 3.2), and 1 pt for the final
formula `C17H31COOH`. Each step is a separate theorem below.
-/

/-- Rubric step 1 (1 pt): the ozonolysis experiment — three different
organic products in equimolar amounts — forces exactly two C=C double
bonds in the fatty acid. -/
theorem ozonolysis_gives_two_double_bonds {d : ℕ}
    (h_ozone : ozonolysisProductCount d = 3) :
    d = 2 := by
  unfold ozonolysisProductCount at h_ozone
  omega

/-- Rubric step 2 (2 pts): the bond count of non-ionised PL1 (255 σ-and-π
bonds) yields the marking scheme's equation 3.2, `4x + y = 99`. -/
theorem bond_count_equation {x y : ℕ}
    (h_bonds : pl1TotalBonds x y = 255) :
    4 * (x : ℚ) + (y : ℚ) = 99 := by
  unfold pl1TotalBonds pl1FragCountA pl1FragCountB pl1FragCountC
    pl1FragCountD fragABonds fragBBonds fragCBonds fragDBonds at h_bonds
  linarith

/-- Rubric step 3 (1 pt) — main target: the fatty acid in PL1 is
`C17H31–COOH`, i.e. its molecular formula is `C18H32O2`.

* `hx` : `R = C_xH_y` is a hydrocarbon substituent, hence contains at
  least one carbon;
* `h_unsat` : R is acyclic and monovalent with `d` C=C bonds as its only
  unsaturation, so `y + 2·d = 2·x + 1` (eq. 3.1 of the marking scheme);
* `h_ozone` : the reductive ozonolysis of RCOOH affords three different
  products in equimolar amounts;
* `h_bonds` : non-ionised PL1 contains 255 σ-and-π bonds in total. -/
theorem icho_2026_t5_a3 {x y d : ℕ} (hx : 1 ≤ x)
    (h_unsat : y + 2 * d = 2 * x + 1)
    (h_ozone : ozonolysisProductCount d = 3)
    (h_bonds : pl1TotalBonds x y = 255) :
    x = 17 ∧ y = 31 ∧ rcoohFormula x y = ⟨18, 32, 2⟩ := by
  have hd : d = 2 := ozonolysis_gives_two_double_bonds h_ozone
  have h99q : 4 * (x : ℚ) + (y : ℚ) = 99 := bond_count_equation h_bonds
  have h99 : 4 * x + y = 99 := by exact_mod_cast h99q
  subst hd
  have hx17 : x = 17 := by omega
  have hy31 : y = 31 := by omega
  refine ⟨hx17, hy31, ?_⟩
  subst hx17; subst hy31; rfl

/-!
### Validation against the recorded answer (not part of the problem contract)
-/

/-- The recorded answer `x = 17`, `y = 31` indeed satisfies the 255-bond
count, confirming that the fragment model above is calibrated to the
official solution (`0.5·1 + 5·2 + 11.5·3 + 4·(3 + 2x + 0.5y) = 255`). -/
example : pl1TotalBonds 17 31 = 255 := by
  norm_num [pl1TotalBonds, pl1FragCountA, pl1FragCountB, pl1FragCountC,
    pl1FragCountD, fragABonds, fragBBonds, fragCBonds, fragDBonds]

/-- The recorded substituent `R = C17H31` is consistent with the
unsaturation relation at `d = 2`: `31 + 2·2 = 2·17 + 1`. -/
example : (31 : ℕ) + 2 * 2 = 2 * 17 + 1 := rfl

/-- The recorded formula of the fatty acid: `C18H32O2`. -/
example : rcoohFormula 17 31 = ⟨18, 32, 2⟩ := rfl

end IChO2026T5A3
