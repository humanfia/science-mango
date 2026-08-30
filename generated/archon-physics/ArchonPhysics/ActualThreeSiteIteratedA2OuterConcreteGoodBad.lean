import ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
import ArchonPhysics.ActualThreeSiteIteratedA2OuterMassBoundaryCollar

/-!
# Concrete two-parameter good/bad decomposition for the three-site outer channel

The good compact has two visible parameters.  `delta` separates the first
and third inverse masses, while `eta` moves all three raw masses into the
interior of their support.  The discarded mass is bounded independently by
`10 delta + 15 eta`; the inverse-function coefficient is only asserted to be
finite and no dependence on either parameter is optimized.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterConcreteGoodBad

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterInverseMassStrip
open ArchonPhysics.ActualThreeSiteIteratedA2OuterMassBoundaryCollar
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The three-fold cube obtained from the inward support cutoff. -/
def threeSiteOuterInnerMassCube (eta : Real) : Set MassTriple :=
  (threeSiteOuterInnerMassSupport eta ×ˢ
    threeSiteOuterInnerMassSupport eta) ×ˢ
      threeSiteOuterInnerMassSupport eta

/-- A globally closed, polynomialized form of inverse-mass separation.
On positive masses it is equivalent to a lower bound on the inverse-mass
difference. -/
def threeSiteOuterPolynomialSeparation (delta : Real) : Set MassTriple :=
  {triple |
    delta * triple.1.1 * triple.2 ≤ |triple.1.1 - triple.2|}

/-- The concrete good compact with separate inverse-strip width `delta` and
support-boundary width `eta`. -/
def threeSiteOuterGoodCompact (delta eta : Real) : Set MassTriple :=
  threeSiteOuterInnerMassCube eta ∩
    threeSiteOuterPolynomialSeparation delta

theorem isCompact_threeSiteOuterInnerMassCube (eta : Real) :
    IsCompact (threeSiteOuterInnerMassCube eta) := by
  unfold threeSiteOuterInnerMassCube threeSiteOuterInnerMassSupport
  exact (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

theorem isClosed_threeSiteOuterPolynomialSeparation (delta : Real) :
    IsClosed (threeSiteOuterPolynomialSeparation delta) := by
  unfold threeSiteOuterPolynomialSeparation
  apply isClosed_le <;> fun_prop

theorem isCompact_threeSiteOuterGoodCompact (delta eta : Real) :
    IsCompact (threeSiteOuterGoodCompact delta eta) := by
  unfold threeSiteOuterGoodCompact
  exact (isCompact_threeSiteOuterInnerMassCube eta).inter_right
    (isClosed_threeSiteOuterPolynomialSeparation delta)

/-- Positive inward cutoff places the concrete compact strictly inside the
three-fold physical support. -/
theorem threeSiteOuterGoodCompact_subset_interior
    {delta eta : Real} (heta : 0 < eta) :
    threeSiteOuterGoodCompact delta eta ⊆
      interior iidMassTripleSupport := by
  intro triple htriple
  rcases htriple with ⟨hinner, _hseparated⟩
  rcases hinner with ⟨⟨hfirst, hmiddle⟩, hthird⟩
  change massLower + eta ≤ triple.1.1 ∧
    triple.1.1 ≤ massUpper - eta at hfirst
  change massLower + eta ≤ triple.1.2 ∧
    triple.1.2 ≤ massUpper - eta at hmiddle
  change massLower + eta ≤ triple.2 ∧
    triple.2 ≤ massUpper - eta at hthird
  rw [iidMassTripleSupport, interior_prod_eq, iidMassPairSupport,
    interior_prod_eq, massSupport, interior_Icc]
  exact ⟨⟨⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩,
      ⟨by linarith, by linarith⟩⟩

/-- Elementary positive-mass identity relating raw and inverse differences. -/
theorem abs_massSub_eq_mul_abs_inverseSub
    {first third : Real} (hfirst : 0 < first) (hthird : 0 < third) :
    |first - third| =
      (first * third) * |first⁻¹ - third⁻¹| := by
  have hidentity :
      first - third = -(first * third) * (first⁻¹ - third⁻¹) := by
    field_simp [ne_of_gt hfirst, ne_of_gt hthird]
    ring
  rw [hidentity, abs_mul, abs_neg, abs_of_pos (mul_pos hfirst hthird)]

/-- Membership in the concrete good compact gives the advertised numerical
inverse-mass separation. -/
theorem delta_le_abs_inverseSub_of_mem_threeSiteOuterGoodCompact
    {delta eta : Real} (heta : 0 < eta)
    {triple : MassTriple}
    (htriple : triple ∈ threeSiteOuterGoodCompact delta eta) :
    delta ≤ |triple.1.1⁻¹ - triple.2⁻¹| := by
  rcases htriple with
    ⟨⟨⟨hfirst, _hmiddle⟩, hthird⟩, hpolynomial⟩
  have hfirstPos : 0 < triple.1.1 :=
    (add_pos massLower_pos heta).trans_le hfirst.1
  have hthirdPos : 0 < triple.2 :=
    (add_pos massLower_pos heta).trans_le hthird.1
  have hproductPos : 0 < triple.1.1 * triple.2 :=
    mul_pos hfirstPos hthirdPos
  change delta * triple.1.1 * triple.2 ≤
    |triple.1.1 - triple.2| at hpolynomial
  rw [abs_massSub_eq_mul_abs_inverseSub hfirstPos hthirdPos] at hpolynomial
  have hpolynomial' :
      (triple.1.1 * triple.2) * delta ≤
        (triple.1.1 * triple.2) *
          |triple.1.1⁻¹ - triple.2⁻¹| := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpolynomial
  exact le_of_mul_le_mul_left hpolynomial' hproductPos

/-- In particular the first and third inverse masses differ everywhere on
the concrete good compact. -/
theorem threeSiteOuterGoodCompact_inverse_separated
    {delta eta : Real} (hdelta : 0 < delta) (heta : 0 < eta) :
    ∀ triple ∈ threeSiteOuterGoodCompact delta eta,
      triple.1.1⁻¹ ≠ triple.2⁻¹ := by
  intro triple htriple
  have habsPos : 0 < |triple.1.1⁻¹ - triple.2⁻¹| :=
    hdelta.trans_le
      (delta_le_abs_inverseSub_of_mem_threeSiteOuterGoodCompact
        heta htriple)
  exact sub_ne_zero.mp (abs_pos.mp habsPos)

/-- On the physical support, failure of the concrete good compact lies in
the inverse strip or in the independently quantified support-boundary
event. -/
theorem support_inter_threeSiteOuterGoodCompact_compl_subset
    (delta eta : Real) :
    iidMassTripleSupport ∩ (threeSiteOuterGoodCompact delta eta)ᶜ ⊆
      threeSiteOuterInverseMassStrip delta ∪
        threeSiteOuterMassBoundaryEvent eta := by
  intro triple htriple
  rcases htriple with ⟨hsupport, hnotGood⟩
  rw [iidMassTripleSupport, iidMassPairSupport] at hsupport
  by_cases hfirstInner :
      triple.1.1 ∈ threeSiteOuterInnerMassSupport eta
  · by_cases hmiddleInner :
        triple.1.2 ∈ threeSiteOuterInnerMassSupport eta
    · by_cases hthirdInner :
          triple.2 ∈ threeSiteOuterInnerMassSupport eta
      · have hnotPolynomial :
            triple ∉ threeSiteOuterPolynomialSeparation delta := by
          intro hpolynomial
          exact hnotGood
            ⟨⟨⟨hfirstInner, hmiddleInner⟩, hthirdInner⟩, hpolynomial⟩
        have hrawLt :
            |triple.1.1 - triple.2| < delta * triple.1.1 * triple.2 :=
          lt_of_not_ge hnotPolynomial
        have hfirstPos : 0 < triple.1.1 :=
          massLower_pos.trans_le hsupport.1.1.1
        have hthirdPos : 0 < triple.2 :=
          massLower_pos.trans_le hsupport.2.1
        have hproductPos : 0 < triple.1.1 * triple.2 :=
          mul_pos hfirstPos hthirdPos
        rw [abs_massSub_eq_mul_abs_inverseSub hfirstPos hthirdPos] at hrawLt
        have hinverseLt :
            |triple.1.1⁻¹ - triple.2⁻¹| < delta := by
          have hrawLt' :
              (triple.1.1 * triple.2) *
                  |triple.1.1⁻¹ - triple.2⁻¹| <
                (triple.1.1 * triple.2) * delta := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using hrawLt
          exact lt_of_mul_lt_mul_left hrawLt' hproductPos.le
        exact Or.inl hinverseLt
      · refine Or.inr ?_
        simp only [threeSiteOuterMassBoundaryEvent,
          threeSiteOuterFirstMassBoundaryEvent,
          threeSiteOuterMiddleMassBoundaryEvent,
          threeSiteOuterThirdMassBoundaryEvent,
          Set.mem_union, Set.mem_prod, Set.mem_univ,
          and_true, true_and]
        exact Or.inr (Or.inr ⟨hsupport.2, hthirdInner⟩)
    · refine Or.inr ?_
      simp only [threeSiteOuterMassBoundaryEvent,
        threeSiteOuterFirstMassBoundaryEvent,
        threeSiteOuterMiddleMassBoundaryEvent,
        threeSiteOuterThirdMassBoundaryEvent,
        Set.mem_union, Set.mem_prod, Set.mem_univ,
        and_true, true_and]
      exact Or.inr (Or.inl ⟨hsupport.1.2, hmiddleInner⟩)
  · refine Or.inr ?_
    simp only [threeSiteOuterMassBoundaryEvent,
      threeSiteOuterFirstMassBoundaryEvent,
      threeSiteOuterMiddleMassBoundaryEvent,
      threeSiteOuterThirdMassBoundaryEvent,
      Set.mem_union, Set.mem_prod, Set.mem_univ,
      and_true, true_and]
    exact Or.inl ⟨hsupport.1.1, hfirstInner⟩

/-- Independent quantitative bad-mass estimate for the explicit compact. -/
theorem iidMassTripleLaw_threeSiteOuterGoodCompact_compl_le
    {delta eta : Real} (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) :
    iidMassTripleLaw (threeSiteOuterGoodCompact delta eta)ᶜ ≤
      10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal eta := by
  have hmono :
      iidMassTripleLaw (threeSiteOuterGoodCompact delta eta)ᶜ ≤
        iidMassTripleLaw
          (threeSiteOuterInverseMassStrip delta ∪
            threeSiteOuterMassBoundaryEvent eta) := by
    apply measure_mono_ae
    filter_upwards [iidMassTriple_mem_support_ae] with triple hsupport
    intro hbad
    exact support_inter_threeSiteOuterGoodCompact_compl_subset
      delta eta ⟨hsupport, hbad⟩
  calc
    iidMassTripleLaw (threeSiteOuterGoodCompact delta eta)ᶜ ≤
        iidMassTripleLaw
          (threeSiteOuterInverseMassStrip delta ∪
            threeSiteOuterMassBoundaryEvent eta) := hmono
    _ ≤ iidMassTripleLaw (threeSiteOuterInverseMassStrip delta) +
        iidMassTripleLaw (threeSiteOuterMassBoundaryEvent eta) :=
      measure_union_le _ _
    _ ≤ 10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal eta :=
      add_le_add
        (iidMassTripleLaw_threeSiteOuterInverseMassStrip_le hdelta)
        (iidMassTripleLaw_threeSiteOuterMassBoundaryEvent_le heta)

/-- Two-parameter quantitative small-ball theorem.  The two bad masses are
displayed independently, and the atlas coefficient is only asserted finite. -/
theorem exists_finiteCoefficient_threeSiteOuter_twoParameter_smallBall
    {delta eta : Real} (hdelta : 0 < delta) (heta : 0 < eta)
    (_hetaWidth : 2 * eta < massUpper - massLower) :
    ∃ coefficient : ENNReal, coefficient ≠ ∞ ∧
      ∀ epsilon : Real, 0 ≤ epsilon →
        iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
          10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal eta +
            coefficient * ENNReal.ofReal epsilon := by
  obtain ⟨coefficient, hcoefficientFinite, hsmallBall⟩ :=
    exists_finiteCoefficient_threeSiteOuter_compact_goodBad_smallBall
      (threeSiteOuterGoodCompact delta eta)
      (isCompact_threeSiteOuterGoodCompact delta eta)
      (threeSiteOuterGoodCompact_subset_interior heta)
      (threeSiteOuterGoodCompact_inverse_separated hdelta heta)
  refine ⟨coefficient, hcoefficientFinite, ?_⟩
  intro epsilon hepsilon
  calc
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
        coefficient * ENNReal.ofReal epsilon +
          iidMassTripleLaw (threeSiteOuterGoodCompact delta eta)ᶜ :=
      hsmallBall epsilon hepsilon
    _ ≤ coefficient * ENNReal.ofReal epsilon +
        (10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal eta) :=
      add_le_add le_rfl
        (iidMassTripleLaw_threeSiteOuterGoodCompact_compl_le
          hdelta.le heta.le)
    _ = 10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal eta +
        coefficient * ENNReal.ofReal epsilon := by ac_rfl

/-- Diagonal choice `eta = delta`.  This is the requested quantifier form:
for every positive strip width there is one finite (unoptimized) coefficient
valid for every nonnegative small-ball radius. -/
theorem exists_finiteCoefficient_threeSiteOuter_diagonal_smallBall
    {delta : Real} (hdelta : 0 < delta)
    (hdeltaWidth : 2 * delta < massUpper - massLower) :
    ∃ coefficient : ENNReal, coefficient ≠ ∞ ∧
      ∀ epsilon : Real, 0 ≤ epsilon →
        iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
          25 * ENNReal.ofReal delta +
            coefficient * ENNReal.ofReal epsilon := by
  obtain ⟨coefficient, hcoefficientFinite, hsmallBall⟩ :=
    exists_finiteCoefficient_threeSiteOuter_twoParameter_smallBall
      hdelta hdelta hdeltaWidth
  refine ⟨coefficient, hcoefficientFinite, ?_⟩
  intro epsilon hepsilon
  calc
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
        10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal delta +
          coefficient * ENNReal.ofReal epsilon :=
      hsmallBall epsilon hepsilon
    _ = 25 * ENNReal.ofReal delta +
        coefficient * ENNReal.ofReal epsilon := by ring

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterConcreteGoodBad
