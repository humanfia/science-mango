import Mathlib

/-!
# IChO 2026, Theory Problem T5 — Subquestion 5.1: parity of the fragment count `n`

## Source contract

58th International Chemistry Olympiad (Tashkent, 2026), Theory Problem T5
("Cardiolipins"), question 5.1 (1.0 pt, classification: tick exactly one
statement).

Visual evidence inspected:

* `T5_page-1.png` (printed page Q5-1): the worked example — the chiral
  phospholipid W assembled from one copy each of fragments a–e; the PL1
  fragment table a–d with the stated quantities `n, 2, 3, 4`; the side
  conditions "R is a hydrocarbon substituent in the fatty acid structure"
  and "PL1 does not contain any peroxide bonds"; and the three options of
  question 5.1.

**Given by the problem.**

* PL1 is a cardiolipin — an acyclic phospholipid — and its non-ionised form
  is assembled *exclusively* from the structural elements a–d, in the stated
  quantities: `n` fragments of type a, 2 of type b, 3 of type c and 4 of
  type d.
* Each fragment is drawn with *wavy lines*: attachment points left by
  "broken bonds".  The census read off the drawings is:
  - a (`~~~–H`): one broken bond, borne by the hydrogen atom;
  - b (phosphate, `O=P(–OH)` with two wavy lines on P): two broken bonds,
    borne by the phosphorus atom;
  - c (glycerol unit, wavy lines on all three of its oxygens): three broken
    bonds, each borne by an oxygen atom;
  - d (acyl unit `~~~–C(=O)–R`): one broken bond, borne by the carbonyl
    carbon.
* When fragments are joined into a molecule, every bond formed involves
  exactly two atoms with broken bonds (this is what the worked example W
  illustrates), so the broken-bond termini pair up completely — the
  non-ionised form has no dangling, ionic open valence.
* PL1 contains no peroxide (O–O) bonds: two oxygen-borne broken bonds are
  never paired with each other.

**Requested conclusion.**  Exactly one of

* (a) `n` is an even number,
* (b) `n` is an odd number,
* (c) `n` can be either an odd or an even number

is correct.  The marking scheme's answer is (b): the fragments of known
multiplicity contribute `2·2 + 3·3 + 4 = 17` atoms with broken bonds, each
bond of the assembly consumes two such atoms, so `n + 17` is even and `n`
is odd.

## Assumption / target split

Assumptions (sourced data or explicit hypotheses):

* the fragment census — `FragmentKind`, `FragmentKind.openEnds`,
  `FragmentKind.endAtom`, `pl1Copies` — is data read off the exam figure
  (wavy-line counts `1, 2, 3, 1` and quantities `n, 2, 3, 4`);
* the assembly model — `OpenEnd`, `Assembly`: an assembly is a complete
  pairing of the broken-bond termini (a fixed-point-free involution, "each
  bond involves two atoms") that forms no peroxide bond;
* the counting principles `card_openEnd` and
  `even_totalOpenEnds_of_assembly` are stated as theorems *over* this model
  (proved in the prover stage via the handshaking argument), not assumed as
  axioms.

Targets (never assumed):

* `totalOpenEnds_eq`: the pool census evaluates to `n + 17`;
* `subquestion_5_1`: any assemblable `n` is odd — option (b) is correct;
* `option_a_incorrect`, `option_c_incorrect`: the two rival options fail.

The worked example W (one copy each of fragments a–e) fixes the assembly
convention only; it imposes no constraint on 5.1 and is not formalized.
-/

namespace IChO2026.T5.A1

/-! ## The fragment census (source page Q5-1) -/

/-- The four structural elements from which the non-ionised form of the
cardiolipin PL1 is assembled (exam figure, problem T5): `a` is `~~~–H`,
`b` the phosphate fragment `O=P(–OH)(~~~)(~~~)`, `c` the glycerol fragment
with three wavy-line oxygens, and `d` the acyl fragment `~~~–C(=O)–R`. -/
inductive FragmentKind where
  | a | b | c | d
  deriving DecidableEq, Repr, Fintype

/-- The chemical element of an atom that bears a broken bond (wavy line) in
the fragment drawings.  All broken bonds of one fragment kind are borne by
atoms of a single element. -/
inductive EndAtom where
  | hydrogen | carbon | oxygen | phosphorus
  deriving DecidableEq, Repr

/-- The element bearing the broken bonds of each fragment kind, as drawn on
page Q5-1: hydrogen for a, phosphorus for b, oxygen for c and the carbonyl
carbon for d. -/
def FragmentKind.endAtom : FragmentKind → EndAtom
  | .a => .hydrogen
  | .b => .phosphorus
  | .c => .oxygen
  | .d => .carbon

/-- The number of atoms with a broken bond (wavy line) in each fragment
kind, as drawn on page Q5-1: a contributes 1, b contributes 2, c contributes
3 and d contributes 1. -/
def FragmentKind.openEnds : FragmentKind → ℕ
  | .a => 1
  | .b => 2
  | .c => 3
  | .d => 1

/-- The quantities stated for the assembly of PL1: `n` fragments of type a,
two of type b, three of type c and four of type d. -/
def pl1Copies (n : ℕ) : FragmentKind → ℕ
  | .a => n
  | .b => 2
  | .c => 3
  | .d => 4

/-- The total number of atoms with broken bonds in the fragment pool used to
assemble PL1 with `n` fragments of type a. -/
def totalOpenEnds (n : ℕ) : ℕ := ∑ k : FragmentKind, pl1Copies n k * k.openEnds

/-! ## The assembly model -/

/-- The type of broken-bond termini ("wavy-line ends") in the fragment pool:
a terminus is specified by its fragment kind, the index of the fragment
copy of that kind, and the index of the terminus on that copy. -/
abbrev OpenEnd (n : ℕ) := Σ k : FragmentKind, Fin (pl1Copies n k) × Fin k.openEnds

instance (n : ℕ) : Fintype (OpenEnd n) := inferInstance

/-- The element of the atom carrying a broken-bond terminus. -/
def OpenEnd.atom {n : ℕ} (e : OpenEnd n) : EndAtom := e.1.endAtom

/-- An assembly of the fragment pool into the non-ionised form of PL1.

Joining fragments consumes the broken bonds pairwise — "each bond involves
two atoms", as in the worked example W — so an assembly is modelled by the
pairing map `bond` on the broken-bond termini, a fixed-point-free
involution: every terminus is matched with a *different* terminus, its
partner in the newly formed bond.  Completeness of the pairing (every
terminus is matched) is the formal content of assembling the *non-ionised*
form: no ionic site with a dangling valence remains.

The side condition "PL1 does not contain any peroxide bonds" forbids
pairing two oxygen-borne termini (`no_peroxide`).  Further chemical
legality constraints (allowed bond types between the element pairs, the
acyclicity of cardiolipins) govern the later subquestions 5.2–5.4 and are
deliberately not imposed here: the parity count of 5.1 rests on the pairing
alone. -/
structure Assembly (n : ℕ) where
  /-- the partner of each broken-bond terminus in its newly formed bond -/
  bond : OpenEnd n → OpenEnd n
  /-- bonding is symmetric: the partner of the partner is the terminus
  itself -/
  involutive : Function.Involutive bond
  /-- a terminus cannot bond to itself: each bond involves two (distinct)
  atoms -/
  fixed_point_free : ∀ e : OpenEnd n, bond e ≠ e
  /-- PL1 contains no peroxide bonds: two oxygen-borne termini are never
  paired with each other -/
  no_peroxide : ∀ e : OpenEnd n,
    ¬ (e.atom = EndAtom.oxygen ∧ (bond e).atom = EndAtom.oxygen)

/-! ## The counting principles -/

/-- The pool census: the number of broken-bond termini equals the total
number of atoms with broken bonds, `Σ_k copies(k) · openEnds(k)`. -/
theorem card_openEnd (n : ℕ) :
    Fintype.card (OpenEnd n) = totalOpenEnds n := by
  rw [Fintype.card_sigma, totalOpenEnds]
  simp [Fintype.card_prod, Fintype.card_fin]

/-- **The counting principle of the marking scheme.**  Each bond of an
assembly involves exactly two atoms with broken bonds, so the total number
of such atoms — the cardinality of the terminus pool — is even.  This is
the handshaking lemma for the pairing `Assembly.bond`: a finite type
carrying a fixed-point-free involution has even cardinality. -/
theorem even_totalOpenEnds_of_assembly {n : ℕ} (A : Assembly n) :
    Even (totalOpenEnds n) := by
  classical
  -- Handshaking: pair each terminus `e` with its bond partner `A.bond e`.
  -- The fibers of the pairing map into `Sym2` all have cardinality 2.
  rw [← card_openEnd n, ← Finset.card_univ]
  set pair : OpenEnd n → Sym2 (OpenEnd n) := fun e => s(e, A.bond e)
  rw [Finset.card_eq_sum_card_image pair Finset.univ]
  have hfiber : ∀ z ∈ Finset.univ.image pair,
      (Finset.univ.filter fun e => pair e = z).card = 2 := by
    intro z hz
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hz
    have hfilter : (Finset.univ.filter fun x => pair x = pair e) = {e, A.bond e} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨hx, -⟩ | ⟨hx, -⟩
        · exact Or.inl hx
        · exact Or.inr hx
      · rintro (rfl | rfl)
        · rfl
        · change s(A.bond e, A.bond (A.bond e)) = s(e, A.bond e)
          rw [A.involutive e]
          exact Sym2.eq_swap
    rw [hfilter]
    exact Finset.card_pair (Ne.symm (A.fixed_point_free e))
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
  exact ⟨Finset.univ.image pair |>.card, by ring⟩

/-- The census of the marking scheme: the fragments of known multiplicity
contribute `2·2 + 3·3 + 4 = 17` atoms with broken bonds, so the pool with
`n` fragments of type a has `n + 17` such atoms in total. -/
theorem totalOpenEnds_eq (n : ℕ) : totalOpenEnds n = n + 17 := by
  have huniv : (Finset.univ : Finset FragmentKind) = {.a, .b, .c, .d} := by
    ext k
    cases k <;> simp
  rw [totalOpenEnds, huniv]
  simp [pl1Copies, FragmentKind.openEnds]

/-! ## Subquestion 5.1: the correct tick is (b) -/

/-- **Subquestion 5.1 — option (b) is correct: `n` is an odd number.**  In
any assembly of the fragment pool into PL1 the pool total `n + 17` of atoms
with broken bonds is even (each bond involves two of them), which forces
`n` to be odd. -/
theorem subquestion_5_1 {n : ℕ} (A : Assembly n) : Odd n := by
  have h := even_totalOpenEnds_of_assembly A
  rw [totalOpenEnds_eq] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r - 9, by omega⟩

/-- Option (a) is incorrect: an assemblable fragment count `n` is never
even. -/
theorem option_a_incorrect {n : ℕ} (A : Assembly n) : ¬ Even n :=
  Nat.not_even_iff_odd.mpr (subquestion_5_1 A)

/-- Option (c) is incorrect: the parity of `n` is not free — no even number
of type-a fragments can be assembled into PL1. -/
theorem option_c_incorrect : ¬ ∃ n : ℕ, Even n ∧ Nonempty (Assembly n) := by
  rintro ⟨n, heven, ⟨A⟩⟩
  exact option_a_incorrect A heven

end IChO2026.T5.A1
