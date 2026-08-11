import Mathlib

/-!
# IChO 2026, Theory Problem T9 (Cyclodextrin Chemistry), Subquestion 9.9

**Source.** 58th International Chemistry Olympiad, Tashkent, Uzbekistan,
2026.  Problem PDF page 88 (printed question page Q9-5); solution page 90.
Visual evidence: `T9_page-5.png` (statement of 9.9) and `T9_page-4.png`
(the Sollogoub hexadifferentiated α-CD scheme and the six-unit α-CD
template used in 9.8).

**Subquestion 9.9.** *Determine the number of all possible arrangements of
the functional groups on a hexadifferentiated α-CD (assume only the
CH₂OH groups have been modified).*  (4.0 pt)

## Chemistry-to-mathematics bridge

* α-Cyclodextrin is a macrocycle of **six** α-D-glucopyranose units joined
  by α-1,4-glycosidic bonds (shared T9 context).  The six units are the six
  *positions* of the ring; they are arranged in a cycle, not in a line.
* *Hexadifferentiated* means each of the six units carries a **different**
  functional group.  The parenthetical assumption says exactly the six
  primary CH₂OH groups (one per unit) have been modified, so there is
  exactly one modification site per unit and hence six sites in total.
  An arrangement is therefore a **bijection** between the six ring
  positions and the six distinct functional groups.
* The macrocycle has no distinguished origin: two arrangements that differ
  only by a rotation of the ring describe the same molecule.  The marking
  scheme accordingly divides the `6!` linear arrangements by the six
  rotations, giving `6! / 6 = 120`.
* **Reflections are not identified.**  Every glucopyranose unit of α-CD is
  chiral (D-glucose), so the ring as a whole is chiral and a reflected
  arrangement is a different compound, not the same one.  Hence the
  quotient is by the cyclic rotation group `ZMod 6` only — never by the
  dihedral group.  This is exactly why the official answer is `6!/6 = 120`
  and not `6!/12 = 60`.

## Assumption / target split

Assumptions (modeled in the definitions below):

* six ring positions (`CDPosition`), arranged in a cycle;
* six pairwise distinct functional groups (`FuncGroup`);
* exactly one modified site per unit (`Arrangement` is an `Equiv`, i.e. a
  bijection between positions and groups);
* molecular identity = equality up to cyclic rotation (`SameMolecule`).

Target (the requested conclusion, proved in the prover stage):

* the number of equivalence classes of arrangements is `6! / 6 = 120`.

The recorded value `120` appears only as the *conclusion* of the final
theorems, never as a premise or definition.
-/

namespace IChO2026.T9.A9

/-- The six glucopyranose units of α-cyclodextrin, i.e. the six positions of
the macrocyclic ring that carry the (modified) primary CH₂OH groups.
Modeled as `ZMod 6` so that the rotational symmetries of the macrocycle are
exactly the translations `x ↦ x + k` for `k : ZMod 6`. -/
abbrev CDPosition : Type := ZMod 6

/-- The six pairwise distinct functional groups of a *hexadifferentiated*
α-CD.  "Hexadifferentiated" means every one of the six primary CH₂OH groups
(one per glucopyranose unit) has been converted into a different functional
group; the abstract labels are modeled as `Fin 6`. -/
abbrev FuncGroup : Type := Fin 6

/-- An *arrangement* of the functional groups on a hexadifferentiated α-CD:
an assignment of a functional group to each ring position.  Because all six
groups are distinct and all six CH₂OH sites are modified, each group occurs
at exactly one position, so an arrangement is a bijection between the six
positions and the six groups. -/
abbrev Arrangement : Type := CDPosition ≃ FuncGroup

/-- Rotation of the macrocycle by `k` units, acting on arrangements: the
functional group seen at position `x` after rotating the ring by `k` is the
group that was at position `x + k`.  This is precomposition with the
translation `Equiv.addRight k`. -/
def rotateBy (k : CDPosition) (σ : Arrangement) : Arrangement :=
  (Equiv.addRight k).trans σ

/-- Two arrangements describe the *same molecule* iff one is obtained from
the other by a rotation of the macrocycle.  Only the six cyclic
translations are quotiented out; reflections are **not**, because the
all-(D-glucose) ring is chiral, so a mirror-image arrangement is a
different compound. -/
def SameMolecule (σ τ : Arrangement) : Prop :=
  ∃ k : CDPosition, τ = rotateBy k σ

/-- Rotation by zero positions leaves an arrangement unchanged. -/
theorem rotateBy_zero (σ : Arrangement) : rotateBy 0 σ = σ := by
  ext x
  change σ (x + 0) = σ x
  rw [add_zero]

/-- Rotations compose: rotating by `j + k` is the same as rotating by `k`
and then by `j`.  Together with `rotateBy_zero` this says the additive
group `ZMod 6` acts on arrangements. -/
theorem rotateBy_add (j k : CDPosition) (σ : Arrangement) :
    rotateBy (j + k) σ = rotateBy j (rotateBy k σ) := by
  ext x
  change σ (x + (j + k)) = σ ((x + j) + k)
  rw [add_assoc]

/-- The equivalence relation on arrangements used for counting distinct
hexadifferentiated α-CDs: equality up to a rotation of the macrocycle. -/
def arrangementSetoid : Setoid Arrangement where
  r := SameMolecule
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro σ
      exact ⟨0, (rotateBy_zero σ).symm⟩
    · rintro σ τ ⟨k, rfl⟩
      exact ⟨-k, by rw [← rotateBy_add, neg_add_cancel, rotateBy_zero]⟩
    · rintro σ τ ρ ⟨j, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + j, (rotateBy_add l j σ).symm⟩

/-- Without quotienting by the ring symmetry, the six distinct functional
groups can be placed on the six labelled positions in `6!` ways — the
"6 linear positions for 6 coloured balls" count of the marking scheme. -/
theorem card_arrangements : Nat.card Arrangement = Nat.factorial 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_equiv (ZMod.finEquiv 6).toEquiv.symm,
    ZMod.card]

/-- Numerical form of `card_arrangements`: there are `720` labelled
arrangements. -/
theorem card_arrangements_eq_720 : Nat.card Arrangement = 720 := by
  rw [card_arrangements]
  decide

/-- The rotation action is *free*: because the six functional groups are
pairwise distinct, no nontrivial rotation of the macrocycle can fix an
arrangement (a rotation by `k ≠ 0` moves every position, and bijectivity of
the arrangement forces the moved group to differ from the original one). -/
theorem rotateBy_eq_self_iff (k : CDPosition) (σ : Arrangement) :
    rotateBy k σ = σ ↔ k = 0 := by
  constructor
  · intro h
    have h2 : rotateBy k σ = rotateBy 0 σ := h.trans (rotateBy_zero σ).symm
    have h3 : (rotateBy k σ) 0 = (rotateBy 0 σ) 0 := by rw [h2]
    change σ (0 + k) = σ (0 + 0) at h3
    rw [zero_add, zero_add] at h3
    exact σ.injective h3
  · rintro rfl
    exact rotateBy_zero σ

/-- Consequently every molecule — every equivalence class of arrangements —
is represented by exactly six labelled arrangements, one for each rotation
of the ring. -/
theorem card_arrangement_class (σ : Arrangement) :
    Nat.card { τ : Arrangement // SameMolecule σ τ } = 6 := by
  have hinj : Function.Injective (fun k : CDPosition => rotateBy k σ) := by
    intro j k h
    have h2 : rotateBy j σ = rotateBy k σ := h
    have h3 : (rotateBy j σ) 0 = (rotateBy k σ) 0 := by rw [h2]
    change σ (0 + j) = σ (0 + k) at h3
    rw [zero_add, zero_add] at h3
    exact σ.injective h3
  have hrange : (fun τ : Arrangement => τ ∈ Set.range (fun k : CDPosition => rotateBy k σ)) =
      fun τ => SameMolecule σ τ := by
    funext τ
    simp only [Set.mem_range]
    apply propext
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
  have e : CDPosition ≃ { τ : Arrangement // SameMolecule σ τ } :=
    (Equiv.ofInjective (fun k : CDPosition => rotateBy k σ) hinj).trans
      (Equiv.subtypeEquivProp hrange)
  calc Nat.card { τ : Arrangement // SameMolecule σ τ }
      = Nat.card CDPosition := (Nat.card_congr e).symm
    _ = 6 := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- **Subquestion 9.9 (official answer `6!/6`).**  The number of all
possible arrangements of the functional groups on a hexadifferentiated
α-CD — six distinct groups on the six CH₂OH positions of the macrocycle,
counted up to rotation of the ring — is `6! / 6`. -/
theorem arrangement_count_eq :
    Nat.card (Quotient arrangementSetoid) = Nat.factorial 6 / 6 := by
  -- The quotient map is 6-to-1: parametrize each labelled arrangement by its
  -- molecule (its rotation class) together with the rotation carrying a fixed
  -- representative of the class to it.  Freeness makes this a bijection
  -- `Quotient arrangementSetoid × CDPosition ≃ Arrangement`.
  have hmk : ∀ (τ : Arrangement) (k : CDPosition),
      Quotient.mk arrangementSetoid (rotateBy k τ) = Quotient.mk arrangementSetoid τ := by
    intro τ k
    apply Quotient.sound
    exact ⟨-k, by rw [← rotateBy_add, neg_add_cancel, rotateBy_zero]⟩
  have hbij : Function.Bijective
      (fun qk : Quotient arrangementSetoid × CDPosition => rotateBy qk.2 qk.1.out) := by
    constructor
    · rintro ⟨q₁, j⟩ ⟨q₂, k⟩ h
      have h' : rotateBy j q₁.out = rotateBy k q₂.out := h
      have e1 : Quotient.mk arrangementSetoid (rotateBy j q₁.out) = q₁ :=
        (hmk q₁.out j).trans q₁.out_eq
      have e2 : Quotient.mk arrangementSetoid (rotateBy k q₂.out) = q₂ :=
        (hmk q₂.out k).trans q₂.out_eq
      have hq : q₁ = q₂ := by rw [← e1, ← e2, h']
      subst hq
      have hjk : j = k := by
        have h3 : (rotateBy j q₁.out) 0 = (rotateBy k q₁.out) 0 := by rw [h']
        change q₁.out (0 + j) = q₁.out (0 + k) at h3
        rw [zero_add, zero_add] at h3
        exact q₁.out.injective h3
      subst hjk
      rfl
    · intro σ
      have h : Quotient.mk arrangementSetoid (Quotient.mk arrangementSetoid σ).out =
          Quotient.mk arrangementSetoid σ := Quotient.out_eq _
      have hsm : SameMolecule (Quotient.mk arrangementSetoid σ).out σ :=
        (Quotient.eq (r := arrangementSetoid)).mp h
      obtain ⟨k, hk⟩ := hsm
      exact ⟨(Quotient.mk arrangementSetoid σ, k), hk.symm⟩
  have hcard : Nat.card (Quotient arrangementSetoid × CDPosition) =
      Nat.card Arrangement := Nat.card_eq_of_bijective _ hbij
  rw [Nat.card_prod, card_arrangements] at hcard
  have h6 : Nat.card CDPosition = 6 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [h6] at hcard
  have hfac : Nat.factorial 6 = 720 := by decide
  omega

/-- **Subquestion 9.9 (official numerical answer).**  The number of all
possible arrangements of the functional groups on a hexadifferentiated
α-CD is `120`. -/
theorem arrangement_count : Nat.card (Quotient arrangementSetoid) = 120 := by
  have h := arrangement_count_eq
  have hfac : Nat.factorial 6 = 720 := by decide
  omega

end IChO2026.T9.A9
