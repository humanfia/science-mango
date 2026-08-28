import ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry

/-!
# Classification of nonzero quadratic FPUT charge fibers

A quadratic free-FPUT phase term carries the sum of two signed coordinate
unit vectors.  Away from zero charge, equality of two such sums determines
the two signed inputs up to permutation.  Zero charge is exceptional: a mode
paired with its opposite phase sign cancels, so many different modes can lie
in the same zero-charge fiber.

This file proves the finite algebraic classification without any injectivity
assumption on frequencies or modes.  It is only a statement about phase
charges and input-swap orbits; no kinetic or thermalization conclusion is
asserted.
-/

namespace ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

noncomputable section

variable {d : Type*} [DecidableEq d]

/-- The two phase signs are distinguished by their integer exponents. -/
theorem phaseSign_eq_of_exponent_eq {left right : PhaseSign}
    (h : left.exponent = right.exponent) : left = right := by
  cases left <;> cases right <;> simp_all [PhaseSign.exponent]

/-- One signed coordinate unit vector determines its mode and sign. -/
theorem signedMode_charge_injective :
    Function.Injective (SignedMode.charge : SignedMode d → d → Int) := by
  intro left right hcharge
  rcases left with ⟨leftMode, leftSign⟩
  rcases right with ⟨rightMode, rightSign⟩
  by_cases hmodes : leftMode = rightMode
  · subst rightMode
    have hexponent : leftSign.exponent = rightSign.exponent := by
      simpa [SignedMode.charge] using
        congrFun hcharge leftMode
    exact congrArg (SignedMode.mk leftMode)
      (phaseSign_eq_of_exponent_eq hexponent)
  · have hzero : leftSign.exponent = 0 := by
      simpa [SignedMode.charge, hmodes] using
        congrFun hcharge leftMode
    cases leftSign <;> simp [PhaseSign.exponent] at hzero

/-- If the two modes on the left are distinct, one of the two signed factors
on the right must equal the first signed factor on the left. -/
theorem first_signed_factor_mem_of_distinct
    (leftMode otherMode rightMode₀ rightMode₁ : d)
    (leftSign otherSign rightSign₀ rightSign₁ : PhaseSign)
    (hdistinct : leftMode ≠ otherMode)
    (hcharge :
      (Pi.single leftMode leftSign.exponent : d → Int) +
          (Pi.single otherMode otherSign.exponent : d → Int) =
        (Pi.single rightMode₀ rightSign₀.exponent : d → Int) +
          (Pi.single rightMode₁ rightSign₁.exponent : d → Int)) :
    (rightMode₀ = leftMode ∧ rightSign₀ = leftSign) ∨
      (rightMode₁ = leftMode ∧ rightSign₁ = leftSign) := by
  have hatLeft := congrFun hcharge leftMode
  by_cases hzeroMode : rightMode₀ = leftMode
  · by_cases honeMode : rightMode₁ = leftMode
    · subst rightMode₀
      subst rightMode₁
      simp [hdistinct] at hatLeft
      cases leftSign <;> cases rightSign₀ <;> cases rightSign₁ <;>
        norm_num [PhaseSign.exponent] at hatLeft
    · left
      refine ⟨hzeroMode, ?_⟩
      have hexponent : rightSign₀.exponent = leftSign.exponent := by
        simpa [hdistinct, hzeroMode, honeMode] using
          hatLeft.symm
      exact phaseSign_eq_of_exponent_eq hexponent
  · by_cases honeMode : rightMode₁ = leftMode
    · right
      refine ⟨honeMode, ?_⟩
      have hexponent : rightSign₁.exponent = leftSign.exponent := by
        simpa [hdistinct, hzeroMode, honeMode] using
          hatLeft.symm
      exact phaseSign_eq_of_exponent_eq hexponent
    · simp [hdistinct, hzeroMode, honeMode] at hatLeft
      cases leftSign <;> norm_num [PhaseSign.exponent] at hatLeft

/-- Two copies of one signed coordinate unit vector can only equal two copies
of the same signed factor. -/
theorem two_equal_signed_factors_classification
    (mode rightMode₀ rightMode₁ : d)
    (sign rightSign₀ rightSign₁ : PhaseSign)
    (hcharge :
      (Pi.single mode sign.exponent : d → Int) + (Pi.single mode sign.exponent : d → Int) =
        (Pi.single rightMode₀ rightSign₀.exponent : d → Int) +
          (Pi.single rightMode₁ rightSign₁.exponent : d → Int)) :
    rightMode₀ = mode ∧ rightSign₀ = sign ∧
      rightMode₁ = mode ∧ rightSign₁ = sign := by
  have hatMode := congrFun hcharge mode
  by_cases hzeroMode : rightMode₀ = mode
  · by_cases honeMode : rightMode₁ = mode
    · subst rightMode₀
      subst rightMode₁
      simp at hatMode
      constructor
      · rfl
      · constructor
        · cases sign <;> cases rightSign₀ <;> cases rightSign₁ <;>
            simp_all [PhaseSign.exponent]
        · constructor
          · rfl
          · cases sign <;> cases rightSign₀ <;> cases rightSign₁ <;>
              simp_all [PhaseSign.exponent]
    · simp [hzeroMode, honeMode] at hatMode
      cases sign <;> cases rightSign₀ <;>
        norm_num [PhaseSign.exponent] at hatMode
  · by_cases honeMode : rightMode₁ = mode
    · simp [hzeroMode, honeMode] at hatMode
      cases sign <;> cases rightSign₁ <;>
        norm_num [PhaseSign.exponent] at hatMode
    · simp [hzeroMode, honeMode] at hatMode
      cases sign <;> norm_num [PhaseSign.exponent] at hatMode

/-- At one common mode, the two signed charges cancel exactly when their
phase signs are opposite. -/
theorem add_signedMode_charge_eq_zero_of_same_mode_iff
    (mode : d) (leftSign rightSign : PhaseSign) :
    SignedMode.charge ⟨mode, leftSign⟩ +
        SignedMode.charge ⟨mode, rightSign⟩ = 0 ↔
      leftSign ≠ rightSign := by
  cases leftSign <;> cases rightSign <;>
    simp [SignedMode.charge, PhaseSign.exponent, ← Pi.single_add]

/-- Equality of two nonzero sums of signed coordinate unit vectors fixes the
two signed factors up to exchange. -/
theorem nonzero_two_signedMode_charge_fiber
    (left₀ left₁ right₀ right₁ : SignedMode d)
    (hcharge : left₀.charge + left₁.charge =
      right₀.charge + right₁.charge)
    (hnonzero : left₀.charge + left₁.charge ≠ 0) :
    (right₀ = left₀ ∧ right₁ = left₁) ∨
      (right₀ = left₁ ∧ right₁ = left₀) := by
  rcases left₀ with ⟨leftMode₀, leftSign₀⟩
  rcases left₁ with ⟨leftMode₁, leftSign₁⟩
  rcases right₀ with ⟨rightMode₀, rightSign₀⟩
  rcases right₁ with ⟨rightMode₁, rightSign₁⟩
  by_cases hleftModes : leftMode₀ = leftMode₁
  · subst leftMode₁
    have hsameSign : leftSign₀ = leftSign₁ := by
      by_contra hopposite
      apply hnonzero
      exact (add_signedMode_charge_eq_zero_of_same_mode_iff
        leftMode₀ leftSign₀ leftSign₁).2 hopposite
    subst leftSign₁
    have hclassified := two_equal_signed_factors_classification
      leftMode₀ rightMode₀ rightMode₁ leftSign₀ rightSign₀ rightSign₁
      (by simpa [SignedMode.charge] using hcharge)
    rcases hclassified with ⟨hm₀, hs₀, hm₁, hs₁⟩
    subst rightMode₀
    subst rightSign₀
    subst rightMode₁
    subst rightSign₁
    exact Or.inl ⟨rfl, rfl⟩
  · have hmatch := first_signed_factor_mem_of_distinct
      leftMode₀ leftMode₁ rightMode₀ rightMode₁
      leftSign₀ leftSign₁ rightSign₀ rightSign₁ hleftModes
      (by simpa [SignedMode.charge] using hcharge)
    rcases hmatch with hmatch | hmatch
    · rcases hmatch with ⟨hm, hs⟩
      subst rightMode₀
      subst rightSign₀
      left
      constructor
      · rfl
      · apply signedMode_charge_injective
        exact (add_left_cancel hcharge).symm
    · rcases hmatch with ⟨hm, hs⟩
      subst rightMode₁
      subst rightSign₁
      right
      constructor
      · apply signedMode_charge_injective
        have hrest :
            SignedMode.charge ⟨leftMode₀, leftSign₀⟩ +
              SignedMode.charge ⟨leftMode₁, leftSign₁⟩ =
            SignedMode.charge ⟨leftMode₀, leftSign₀⟩ +
              SignedMode.charge ⟨rightMode₀, rightSign₀⟩ := by
          calc
            SignedMode.charge ⟨leftMode₀, leftSign₀⟩ +
                SignedMode.charge ⟨leftMode₁, leftSign₁⟩ =
              SignedMode.charge ⟨rightMode₀, rightSign₀⟩ +
                SignedMode.charge ⟨leftMode₀, leftSign₀⟩ := hcharge
            _ = SignedMode.charge ⟨leftMode₀, leftSign₀⟩ +
                SignedMode.charge ⟨rightMode₀, rightSign₀⟩ := add_comm _ _
        exact (add_left_cancel hrest).symm
      · rfl

/-- The binary encoding of phase versus conjugate phase is injective. -/
theorem binaryPhaseSign_injective : Function.Injective binaryPhaseSign := by
  intro left right hsign
  fin_cases left <;> fin_cases right <;> simp_all

/-- Equality of the two ordered signed inputs determines a quadratic phase
term exactly. -/
theorem quadraticPhaseTerm_eq_of_signedInputs_eq
    {N : Nat} [NeZero N] (left right : QuadraticPhaseTerm N)
    (hzero :
      binarySignedMode (right.1 0) right.2.1 =
        binarySignedMode (left.1 0) left.2.1)
    (hone :
      binarySignedMode (right.1 1) right.2.2 =
        binarySignedMode (left.1 1) left.2.2) :
    right = left := by
  have hmzero := congrArg SignedMode.mode hzero
  have hmone := congrArg SignedMode.mode hone
  have hszero := binaryPhaseSign_injective
    (congrArg SignedMode.sign hzero)
  have hsone := binaryPhaseSign_injective
    (congrArg SignedMode.sign hone)
  apply Prod.ext
  · funext r
    fin_cases r
    · exact hmzero
    · exact hmone
  · apply Prod.ext
    · exact hszero
    · exact hsone

/-- A same-mode pair with opposite binary phase sectors is precisely the
zero-charge degeneracy excluded by the nonzero-fiber theorem. -/
theorem quadraticPhaseCharge_eq_zero_of_sameMode_oppositeSigns
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N)
    (hmodes : term.1 0 = term.1 1)
    (hsigns : term.2.1 ≠ term.2.2) :
    quadraticPhaseCharge term = 0 := by
  have hbinary :
      binaryPhaseSign term.2.1 ≠ binaryPhaseSign term.2.2 := by
    intro h
    exact hsigns (binaryPhaseSign_injective h)
  unfold quadraticPhaseCharge binarySignedMode
  rw [← hmodes]
  exact (add_signedMode_charge_eq_zero_of_same_mode_iff
    (term.1 0) (binaryPhaseSign term.2.1)
      (binaryPhaseSign term.2.2)).2 hbinary

/-- Nonzero quadratic FPUT charge fibers are exactly the two possible ordered
representatives of one input-swap orbit. -/
theorem quadraticPhaseCharge_eq_nonzero_imp_eq_or_swap
    {N : Nat} [NeZero N] (left right : QuadraticPhaseTerm N)
    (hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right)
    (hnonzero : quadraticPhaseCharge left ≠ 0) :
    right = left ∨ right = swapQuadraticPhaseTerm left := by
  have hclassified := nonzero_two_signedMode_charge_fiber
    (binarySignedMode (left.1 0) left.2.1)
    (binarySignedMode (left.1 1) left.2.2)
    (binarySignedMode (right.1 0) right.2.1)
    (binarySignedMode (right.1 1) right.2.2)
    (by simpa only [quadraticPhaseCharge] using hcharge)
    (by simpa only [quadraticPhaseCharge] using hnonzero)
  rcases hclassified with hsame | hswap
  · exact Or.inl (quadraticPhaseTerm_eq_of_signedInputs_eq
      left right hsame.1 hsame.2)
  · right
    apply quadraticPhaseTerm_eq_of_signedInputs_eq
      (swapQuadraticPhaseTerm left) right
    · simpa using hswap.1
    · simpa using hswap.2

/-- Equal nonzero charge places the right term in the left term input-swap
orbit. -/
theorem mem_quadraticSwapOrbit_of_charge_eq_of_nonzero
    {N : Nat} [NeZero N] (left right : QuadraticPhaseTerm N)
    (hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right)
    (hnonzero : quadraticPhaseCharge left ≠ 0) :
    right ∈ quadraticSwapOrbit left := by
  rcases quadraticPhaseCharge_eq_nonzero_imp_eq_or_swap
      left right hcharge hnonzero with hsame | hswap
  · simp [quadraticSwapOrbit, hsame]
  · simp [quadraticSwapOrbit, hswap]

/-- Therefore a same-charge pair belonging to distinct input-swap orbits can
only occur in the exceptional zero-charge fiber. -/
theorem quadraticPhaseCharge_eq_zero_of_eq_and_not_mem_swapOrbit
    {N : Nat} [NeZero N] (left right : QuadraticPhaseTerm N)
    (hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right)
    (hnotmem : right ∉ quadraticSwapOrbit left) :
    quadraticPhaseCharge left = 0 := by
  by_contra hnonzero
  exact hnotmem
    (mem_quadraticSwapOrbit_of_charge_eq_of_nonzero
      left right hcharge hnonzero)

end

end ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
