import Mathlib

/-!
# IChO 2026, Problem T9, Subquestion 9.7 — m/z of the [M+Na]⁺ peaks of the
hexo-5-enose degradation products of **L**

## Source

58th International Chemistry Olympiad, Tashkent 2026, Theory problem T9
(Cyclodextrin Chemistry), subquestion 9.7 (6 points).

> To confirm the positions of debenzylation, **L** was subjected to the
> "hexo-5-enose degradation" reaction, as shown below. The products were then
> analysed by mass spectrometry.
>
> **9.7** Calculate the m/z value for the two [M+Na]⁺ peaks that were observed
> for the degradation products from **L**. **Use** integer values of atomic
> mass. (6.0 pt)

## Chemical content (from problem pages Q9-3/Q9-4 and the shared context)

* β-Cyclodextrin is a cyclic oligomer of **seven** α-D-glucopyranosyl units
  joined by α-1,4-glycosidic bonds.
* **L** is the per-benzylated β-CD derivative of the Sinay et al. synthesis
  (subquestions 9.5–9.6): DIBAL-H (2 equiv) reductively debenzylates exactly
  **two** primary CH₂OBn positions — the protic group released at unit 1
  directs the second debenzylation to **unit 4** (unit 4 is available in the
  β-CD ring, so the 1,4-pattern is realized).  Hence **L** carries exactly two
  free primary CH₂OH groups, at ring units 1 and 4.
* The degradation sequence 1) I₂, P(C₆H₅)₃; 2) Zn, C₃H₇OH; 3) NaBH₄;
  4) Ac₂O, Py converts each unit bearing a free primary OH into a
  hexo-5-enose-derived (ring-opened, reduced, acetylated) "black" unit and
  cleaves the macrocycle at the two transformed units.  Because the ring is
  cut at both black units, the two observed products are the two oriented
  cyclic paths between the sites: each product consists of the black unit at
  the start of the path, the intact "white" units lying strictly between the
  two sites along that path, and one acetoxy (OAc) cap installed on the newly
  exposed end by the final Ac₂O/Py step.
* The scheme on page Q9-4 prints the fragment formulas: white (intact
  per-O-benzyl glucopyranosyl) unit = C₂₇H₂₈O₅; black (hexo-5-enose-derived)
  unit = C₂₂H₂₅O₄; the acetoxy cap contributes C₂H₃O₂.

## Requested outputs

* m/z of the two observed [M+Na]⁺ peaks, using integer atomic masses
  (C = 12, H = 1, O = 16, Na = 23).

## Assumption/target split

* Assumptions (sourced data and previous-part structural fact, restated as
  explicit hypotheses because the dependency policy is
  `natural_language_prerequisite_only`): the printed fragment formulas
  C₂₇H₂₈O₅ / C₂₂H₂₅O₄, the acetoxy group formula C₂H₃O₂, the integer atomic
  masses, the seven-membered cyclodextrin ring, and the positions of the two
  debenzylated sites of **L** (units 1 and 4).
* The white-unit counts (2 and 3) are **not** assumed: they are derived from
  the two oriented cyclic path lengths between the sites (3 and 4 glycosidic
  steps, hence 2 and 3 units strictly between them) via the cleavage/capping
  relation `cleavageFragment`.
* Targets (never assumed): the neutral molecular formulas C₇₈H₈₄O₁₆ /
  C₁₀₅H₁₁₂O₂₁ and the requested sodiated m/z values.
-/

namespace IChO2026.T9A7

/-- The elements occurring in subquestion 9.7: the degradation products are
hydrocarbon/oxygen compounds, and the mass spectrum is taken as the sodium
adduct [M+Na]⁺. -/
inductive Element
  | C | H | O | Na
  deriving DecidableEq, Repr

/-- Integer (nominal) atomic masses, as instructed by the problem
("**Use** integer values of atomic mass") with the standard IChO periodic
table: C = 12, H = 1, O = 16, Na = 23. -/
def integerAtomicMass : Element → ℕ
  | .C => 12
  | .H => 1
  | .O => 16
  | .Na => 23

/-- A molecular (or functional-group) formula over {C, H, O}: the number of
atoms of each element.  This is the source's abstraction level — the problem
hands out and asks for plain empirical formulas. -/
structure MolFormula where
  /-- number of carbon atoms -/
  nC : ℕ
  /-- number of hydrogen atoms -/
  nH : ℕ
  /-- number of oxygen atoms -/
  nO : ℕ
  deriving DecidableEq, Repr

/-- Componentwise addition of formulas: the formula of a composite species is
the sum of the formulas of its constituent fragments. -/
instance : Add MolFormula where
  add f g := ⟨f.nC + g.nC, f.nH + g.nH, f.nO + g.nO⟩

/-- Scaling a formula by a stoichiometric coefficient (e.g. `2 • f` for two
copies of fragment `f`). -/
instance : SMul ℕ MolFormula where
  smul n f := ⟨n * f.nC, n * f.nH, n * f.nO⟩

/-- Nominal neutral mass of a formula: the sum over elements of
(atom count × integer atomic mass). -/
def neutralMass (f : MolFormula) : ℕ :=
  f.nC * integerAtomicMass .C + f.nH * integerAtomicMass .H +
    f.nO * integerAtomicMass .O

/-- Nominal mass of the sodiated adduct ion [M+Na]⁺: neutral mass plus the
integer mass of sodium (electron mass neglected, as is standard in MS
bookkeeping). -/
def sodiatedAdductMass (f : MolFormula) : ℕ :=
  neutralMass f + integerAtomicMass .Na

/-- Mass-to-charge ratio m/z (in thomson) of an ion of the given nominal mass
and charge number `z`.  For [M+Na]⁺ the charge is `z = 1`, so m/z equals the
adduct mass; keeping `z` explicit preserves the definition of the readout. -/
def mz (mass : ℕ) (z : ℕ) : ℚ := (mass : ℚ) / (z : ℚ)

/-- "Unit 1" fragment (white sphere): an intact per-O-benzylated
glucopyranosyl unit of the cyclodextrin chain, with the formula C₂₇H₂₈O₅
printed under the degradation scheme on page Q9-4. -/
def unit1Fragment : MolFormula := ⟨27, 28, 5⟩

/-- "Unit 2" fragment (black sphere): the hexo-5-enose-derived unit produced
from a glucopyranosyl unit bearing a free primary OH by the
I₂/PPh₃ → Zn → NaBH₄ → Ac₂O/Py sequence (ring opening, reduction,
acetylation), with the formula C₂₂H₂₅O₄ printed under the degradation scheme
on page Q9-4. -/
def unit2Fragment : MolFormula := ⟨22, 25, 4⟩

/-- The acetoxy group CH₃C(O)O–, formula C₂H₃O₂, installed on each product by
the final Ac₂O/Py acetylation step (the "OAc" cap of the official marking
scheme, counted once per degradation product). -/
def acetoxyGroup : MolFormula := ⟨2, 3, 2⟩

/-- The cyclic positions of the seven glucopyranosyl units of a β-cyclodextrin
ring, labelled `0, …, 6` corresponding to printed units `1, …, 7`; the ring
structure makes `ZMod 7` the natural carrier (position `i + 1` is the next
unit along the α-1,4-glycosidic chain). -/
abbrev RingPosition := ZMod 7

/-- The number of glycosidic steps from unit `a` to unit `b` along the
oriented macrocyclic ring (0 when `a = b`, otherwise in `{1, …, 6}`); the two
oriented cyclic path lengths between distinct sites `a`, `b` sum to 7. -/
def cyclicDistance (a b : RingPosition) : ℕ := (b - a).val

/-- The number of intact (white) glucopyranosyl units lying strictly between
unit `a` and unit `b` on the oriented cyclic path from `a` to `b`. -/
def whiteUnitsBetween (a b : RingPosition) : ℕ := cyclicDistance a b - 1

/-- The hexo-5-enose cleavage/capping relation: cutting the macrocycle at the
two transformed (black) units releases, for the oriented path from black unit
`a` to black unit `b`, the fragment consisting of

* the white units lying strictly between `a` and `b` on that path
  (`whiteUnitsBetween a b` copies of `unit1Fragment`),
* the single black unit `a` itself (`unit2Fragment`), and
* one acetoxy cap (`acetoxyGroup`) installed on the end exposed by the
  cleavage.

The two observed products of **L** are `cleavageFragment s₁ s₂` and
`cleavageFragment s₂ s₁`, where `s₁`, `s₂` are its two debenzylated sites. -/
def cleavageFragment (a b : RingPosition) : MolFormula :=
  whiteUnitsBetween a b • unit1Fragment + unit2Fragment + acetoxyGroup

/-- Molecular-formula bookkeeping for the two degradation products of **L**.

The site hypotheses restate the structural fact about **L** from the previous
part (Sinay et al. direction): its two free primary OH groups — hence the two
black units after degradation — sit at ring units 1 and 4 (positions 0 and 3).
The product hypotheses identify the two observed products with the two
oriented cleavage fragments.  The white-unit counts (2 and 3) and the neutral
formulas C₇₈H₈₄O₁₆ / C₁₀₅H₁₁₂O₂₁ are conclusions, not premises. -/
theorem degradation_products_formula
    (s₁ s₂ : RingPosition)
    (hs₁ : s₁ = 0) (hs₂ : s₂ = 3)
    (P₁ P₂ : MolFormula)
    (hP₁ : P₁ = cleavageFragment s₁ s₂)
    (hP₂ : P₂ = cleavageFragment s₂ s₁) :
    P₁ = ⟨78, 84, 16⟩ ∧ P₂ = ⟨105, 112, 21⟩ := by
  -- Substituting the sites (0 and 3 in `ZMod 7`) and the product formulas,
  -- both conjunctions become closed computations: the oriented distances are
  -- `(3 - 0 : ZMod 7).val = 3` and `(0 - 3 : ZMod 7).val = 4`, so the white-unit
  -- counts are 2 and 3, and the fragment bookkeeping gives
  -- `2 • C₂₇H₂₈O₅ + C₂₂H₂₅O₄ + C₂H₃O₂ = C₇₈H₈₄O₁₆` and
  -- `3 • C₂₇H₂₈O₅ + C₂₂H₂₅O₄ + C₂H₃O₂ = C₁₀₅H₁₁₂O₂₁`.
  subst hs₁ hs₂ hP₁ hP₂
  decide

/-- Subquestion 9.7, requested outputs: the m/z values of the two observed
[M+Na]⁺ peaks of the degradation products of **L** are 1299 (the fragment
spanning the short 1→4 path, two white units) and 1731 (the fragment spanning
the long 4→1 path, three white units), using integer atomic masses; [M+Na]⁺
is singly charged, so `z = 1`. -/
theorem degradation_products_sodiated_mz
    (s₁ s₂ : RingPosition)
    (hs₁ : s₁ = 0) (hs₂ : s₂ = 3)
    (P₁ P₂ : MolFormula)
    (hP₁ : P₁ = cleavageFragment s₁ s₂)
    (hP₂ : P₂ = cleavageFragment s₂ s₁) :
    mz (sodiatedAdductMass P₁) 1 = 1299 ∧
    mz (sodiatedAdductMass P₂) 1 = 1731 := by
  -- The neutral formulas from the companion theorem give the sodiated masses
  -- `78·12 + 84·1 + 16·16 + 23 = 1299` and `105·12 + 112·1 + 21·16 + 23 = 1731`;
  -- with `z = 1` each m/z equals the adduct mass.
  obtain ⟨rfl, rfl⟩ := degradation_products_formula s₁ s₂ hs₁ hs₂ P₁ P₂ hP₁ hP₂
  constructor <;>
    norm_num [mz, sodiatedAdductMass, neutralMass, integerAtomicMass]

end IChO2026.T9A7
