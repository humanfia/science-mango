import Mathlib

/-!
# IChO 2026, Theory Problem T1 — Subquestion 1.3: identifying **W**

## Source contract

58th International Chemistry Olympiad (Tashkent, 2026), Theory Problem T1
("A Journey through Time: The Secrets of Avicenna"), Part 1 ("The blue
elixir"), question 1.3 (3.0 pt).

Visual evidence inspected:

* `T1_page-2.png` (printed page Q1-2): the table of the four plants and the
  ten numbered extractable compounds, with structures and molecular formulas.
* `T1_page-3.png` (printed page Q1-3): the text of questions 1.2 and 1.3,
  including the isotope assumptions and the measured ratio.

**Given by the problem.**

* The elixir consists of four substances X, Y, Z and W; every component is
  one of the ten numbered compounds of the source table.
* W gives a characteristic colour change with aqueous Fe³⁺.
* The mass spectrum of W shows `[M]⁺ : [M+1]⁺ = 9 : 1`, where `M` is the
  molecular ion.
* Carbon consists exclusively of ¹²C and ¹³C, the natural abundance of ¹²C
  is 98.9 %, and all other elements are monoisotopic.

**Requested conclusions.**

1. The number `n` of carbon atoms of W, determined from the
   mass-spectrometric data ("show your calculations" — the isotope-ratio
   equation and its solution), and
2. the identity of W.

## Assumption / target split

Assumptions (sourced data or explicit hypotheses):

* the candidate table itself — `Compound`, `Compound.formula`,
  `Compound.hasPhenol`, `Compound.plants` (structures read off page Q1-2:
  only compounds 1 and 5 carry an –OH directly on a benzene ring);
* the isotope abundances — `abundanceC12` (given), `abundanceC13` (forced by
  the exclusivity clause `p₁₂ + p₁₃ = 1`);
* the two-isotope peak model — `probMolecularIon`, `probM1Ion`,
  `relativeIntensityM1` (M needs all-¹²C; M+1 needs exactly one ¹³C, since
  all other elements are monoisotopic);
* the measured ratio `measuredRatio = 1/9`;
* the Fe³⁺/phenol characteristic-test law — an explicit hypothesis `htest`
  of the final theorems (a chemical test law is not a mathematical axiom).

Targets (never assumed):

* `carbon_count_eq_ten`: the determined carbon number is `10`;
* `W_identification`, `subquestion_1_3`: W is compound 5 (eugenol).

The exact equation `n · p₁₃ / p₁₂ = 1/9` has the *real* solution
`p₁₂ / (9 · p₁₃) = 989/99 ≈ 9.99`, which no natural number satisfies exactly;
the marking scheme rounds it to the nearest whole atom count.  The rounding
guarantee is therefore recorded explicitly (`carbonCountEstimate_near_ten`,
and the half-width hypothesis of `carbon_count_eq_ten`) rather than being
hidden in an unsatisfiable exact-equality premise.
-/

namespace IChO2026.T1.A3

/-! ## The candidate table (source page Q1-2) -/

/-- The four plants of Avicenna's laboratory listed in the source table. -/
inductive Plant where
  | zingiber
  | hypericum
  | chamomilla
  | artemisia
  deriving DecidableEq, Repr, Fintype

/-- The ten numbered candidate compounds of the source table.  The elixir
components X, Y, Z and W are drawn from these ten. -/
inductive Compound where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Repr, Fintype

/-- Molecular formula over C, H and O — the only elements occurring in the
candidate table. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- The molecular formulas printed in the source table (page Q1-2). -/
def Compound.formula : Compound → MolecularFormula
  | .c1 => ⟨11, 14, 3⟩
  | .c2 => ⟨10, 18, 1⟩
  | .c3 => ⟨10, 18, 1⟩
  | .c4 => ⟨6, 12, 1⟩
  | .c5 => ⟨10, 12, 2⟩
  | .c6 => ⟨10, 18, 1⟩
  | .c7 => ⟨14, 16, 0⟩
  | .c8 => ⟨15, 24, 0⟩
  | .c9 => ⟨10, 16, 1⟩
  | .c10 => ⟨10, 18, 1⟩

/-- The number of carbon atoms of a candidate compound. -/
def Compound.carbonCount (c : Compound) : ℕ := c.formula.carbon

/-- The plants from which each candidate can be extracted, as printed in the
source table.  Compound 3 appears in the rows of Zingiber, Chamomilla and
Artemisia alike. -/
def Compound.plants : Compound → List Plant
  | .c1 => [.zingiber]
  | .c2 => [.zingiber]
  | .c3 => [.zingiber, .chamomilla, .artemisia]
  | .c4 => [.hypericum]
  | .c5 => [.hypericum]
  | .c6 => [.hypericum]
  | .c7 => [.chamomilla]
  | .c8 => [.chamomilla]
  | .c9 => [.artemisia]
  | .c10 => [.artemisia]

/-- Phenolic candidates: an –OH group bound directly to a benzene ring, as
drawn on page Q1-2.  Among the ten candidates only compound 1 (zingerone)
and compound 5 (eugenol) are phenolic; the –OH of compounds 2, 4 and 6 is
aliphatic. -/
def Compound.hasPhenol : Compound → Bool
  | .c1 | .c5 => true
  | _ => false

/-- The marking scheme's name for compound 1 (Zingiber, C₁₁H₁₄O₃). -/
def zingerone : Compound := .c1

/-- The marking scheme's name for compound 5 (Hypericum, C₁₀H₁₂O₂). -/
def eugenol : Compound := .c5

/-! ## The two-isotope carbon model -/

/-- The natural abundance of ¹²C given by the problem: 98.9 %. -/
noncomputable def abundanceC12 : ℝ := 0.989

/-- The abundance of ¹³C.  The problem states that carbon consists
exclusively of ¹²C and ¹³C, so the ¹³C abundance is `1 − 0.989 = 0.011`. -/
noncomputable def abundanceC13 : ℝ := 1 - abundanceC12

/-- Probability that the molecular ion of a compound with `n` carbon atoms
sits at mass `M`: all `n` carbons are ¹²C and every other element is
monoisotopic. -/
noncomputable def probMolecularIon (n : ℕ) : ℝ := abundanceC12 ^ n

/-- Probability of the `M + 1` ion of a compound with `n` carbon atoms:
exactly one of the `n` carbons is ¹³C (`Nat.choose n 1` placements). -/
noncomputable def probM1Ion (n : ℕ) : ℝ :=
  (Nat.choose n 1 : ℝ) * abundanceC12 ^ (n - 1) * abundanceC13

/-- The relative intensity `I([M+1]⁺) / I([M]⁺)` predicted by the
two-isotope model for `n` carbon atoms. -/
noncomputable def relativeIntensityM1 (n : ℕ) : ℝ :=
  probM1Ion n / probMolecularIon n

/-- The measured intensity ratio `I([M+1]⁺) / I([M]⁺)` of W: the problem
reports `[M]⁺ : [M+1]⁺ = 9 : 1`. -/
noncomputable def measuredRatio : ℝ := 1 / 9

theorem abundanceC12_pos : 0 < abundanceC12 := by
  norm_num [abundanceC12]

theorem abundanceC12_lt_one : abundanceC12 < 1 := by
  norm_num [abundanceC12]

theorem abundanceC13_pos : 0 < abundanceC13 := by
  norm_num [abundanceC13, abundanceC12]

theorem abundanceC13_lt_one : abundanceC13 < 1 := by
  norm_num [abundanceC13, abundanceC12]

theorem probMolecularIon_pos (n : ℕ) : 0 < probMolecularIon n := by
  unfold probMolecularIon
  exact pow_pos abundanceC12_pos n

/-- The isotope-ratio equation ("show your calculations"): under the
two-isotope model the relative `M + 1` intensity of `n` carbons simplifies
to `n · p₁₃ / p₁₂`.  This is Equation (1) of the marking scheme,
`p₁₂ ⁿ / (n · p₁₂ ⁿ⁻¹ · p₁₃) = 9`, cleared of denominators. -/
theorem relativeIntensityM1_eq (n : ℕ) :
    relativeIntensityM1 n = (n : ℝ) * abundanceC13 / abundanceC12 := by
  have h12 : (abundanceC12 : ℝ) ≠ 0 := ne_of_gt abundanceC12_pos
  cases n with
  | zero =>
      simp [relativeIntensityM1, probM1Ion, probMolecularIon]
  | succ m =>
      have hm : (abundanceC12 : ℝ) ^ m ≠ 0 := pow_ne_zero m h12
      rw [relativeIntensityM1, probM1Ion, probMolecularIon, Nat.choose_one_right]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp

/-- The real-valued solution of the isotope-ratio equation at the measured
ratio, `p₁₂ / (9 · p₁₃) = 989/99 ≈ 9.99`. -/
noncomputable def carbonCountEstimate : ℝ := abundanceC12 / (9 * abundanceC13)

/-- Solving the isotope-ratio equation over `ℝ`: the equation at the
measured ratio and the estimate determine each other. -/
theorem carbonCountEstimate_spec (x : ℝ) :
    x * abundanceC13 / abundanceC12 = measuredRatio ↔ x = carbonCountEstimate := by
  have h12 : abundanceC12 ≠ 0 := ne_of_gt abundanceC12_pos
  have h13 : abundanceC13 ≠ 0 := ne_of_gt abundanceC13_pos
  constructor
  · intro h
    have hx : x = measuredRatio * abundanceC12 / abundanceC13 := by
      rw [← h]
      field_simp
    rw [hx]
    unfold carbonCountEstimate measuredRatio
    field_simp
  · intro h
    rw [h]
    unfold carbonCountEstimate measuredRatio
    field_simp

/-- The real solution `0.989 / (9 · 0.011) = 989/99 ≈ 9.99` lies within one
half of `10`, so integrality of atom counts rounds it to `10`. -/
theorem carbonCountEstimate_near_ten : |carbonCountEstimate - 10| < 1 / 2 := by
  have h : carbonCountEstimate = (989 : ℝ) / 99 := by
    norm_num [carbonCountEstimate, abundanceC13, abundanceC12]
  rw [h]
  norm_num

/-- **Determination of n (part 1 of the question).**  The whole number of
carbon atoms fixed by the mass-spectrometric estimate is `10`. -/
theorem carbon_count_eq_ten {n : ℕ}
    (h : |(n : ℝ) - carbonCountEstimate| < 1 / 2) : n = 10 := by
  have h2 := carbonCountEstimate_near_ten
  have h3 : |(n : ℝ) - 10| < 1 := by
    have hrewrite : (n : ℝ) - 10 =
        ((n : ℝ) - carbonCountEstimate) + (carbonCountEstimate - 10) := by ring
    calc |(n : ℝ) - 10|
        = |((n : ℝ) - carbonCountEstimate) + (carbonCountEstimate - 10)| := by
          rw [hrewrite]
      _ ≤ |(n : ℝ) - carbonCountEstimate| + |carbonCountEstimate - 10| :=
          abs_add_le _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add h h2
      _ = 1 := by norm_num
  rw [abs_lt] at h3
  have h9 : 9 < n := by
    have h9r : (9 : ℝ) < (n : ℝ) := by linarith [h3.1]
    exact_mod_cast h9r
  have h11 : n < 11 := by
    have h11r : (n : ℝ) < (11 : ℝ) := by linarith [h3.2]
    exact_mod_cast h11r
  omega

/-! ## The Fe³⁺ colour test and the identification of W -/

/-- The phenol filter of the candidate table: a candidate is phenolic iff it
is compound 1 (zingerone) or compound 5 (eugenol). -/
theorem hasPhenol_iff (c : Compound) :
    c.hasPhenol = true ↔ c = zingerone ∨ c = eugenol := by
  cases c <;> simp [Compound.hasPhenol, zingerone, eugenol]

/-- **Identification of W (part 2 of the question).**  If `w` responds to
the Fe³⁺ colour test, the characteristic-test law forces `w` to be phenolic,
and the determined carbon number `10` singles out compound 5, eugenol. -/
theorem W_identification (givesColourWithFe3 : Compound → Prop) (w : Compound)
    (hcolour : givesColourWithFe3 w)
    (htest : ∀ c : Compound, givesColourWithFe3 c → c.hasPhenol = true)
    (hcarbon : w.carbonCount = 10) :
    w = eugenol := by
  have hp : w.hasPhenol = true := htest w hcolour
  rw [hasPhenol_iff] at hp
  rcases hp with h | h
  · subst h
    simp [zingerone, Compound.carbonCount, Compound.formula] at hcarbon
  · exact h

/-- **Subquestion 1.3, complete.**  From the Fe³⁺ colour observation, the
characteristic-test law, and the mass-spectrometric estimate of the carbon
number, W has `10` carbon atoms and is eugenol (compound 5). -/
theorem subquestion_1_3 (givesColourWithFe3 : Compound → Prop) (w : Compound)
    (hcolour : givesColourWithFe3 w)
    (htest : ∀ c : Compound, givesColourWithFe3 c → c.hasPhenol = true)
    (hmass : |(w.carbonCount : ℝ) - carbonCountEstimate| < 1 / 2) :
    w.carbonCount = 10 ∧ w = eugenol := by
  have hcarbon : w.carbonCount = 10 := carbon_count_eq_ten hmass
  exact ⟨hcarbon, W_identification givesColourWithFe3 w hcolour htest hcarbon⟩

end IChO2026.T1.A3
