import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Family8Grounding.Family8AverageMultiplicityToUnionLowerV1
import Family8Grounding.Family8Prop66AFrostmanUnionVolumeAverageAdapterV1
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

/-!
# The low-average branch and final algebra for the plank Frostman estimate

This module isolates two non-analytic parts of the paper's `plankF` lemma.

* Density together with the low-average alternative
  `averageMultiplicity <= a^(-eta)` gives a literal shaded-union floor.
* The paper's plank-union lower bound gives the Family 6
  `convexPlankFrostmanFactor` average-multiplicity bound by exact power
  cancellation and the certified plank-volume upper bound.

The high-average row selection and the use of the source `FrostmanProperty`
are intentionally absent.  In particular, this file does not import or
consume `ConvexPlankFrostmanBoundAtFixedGeometry` or any Family 7 analytic
hypothesis.

The final cancellation theorem assumes `CF` and `M` are positive finite
bases.  This is the exact domain on which the positive and negative real
powers in the two displayed paper factors cancel.  The degenerate `CF = 0`,
`CF = infinity`, or `M = 0` cases are not silently assigned a cancellation
identity; an eventual analytic producer may discharge or split those cases
from its geometric hypotheses.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8PlankFrostmanLowAverageFinalAlgebraV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8AverageMultiplicityToUnionLowerV1
open Family8Prop66AFrostmanUnionVolumeAverageAdapterV1

noncomputable section

variable {index : Type} [Fintype index] [DecidableEq index]
variable {a b : NNReal}

/-- The literal union-volume right-hand side in the paper's plank Frostman
lemma:

`a^epsilon * CF^(beta/2-1) * b^(2*beta) *
  (M^(-1) * (b^2 * #P))^(beta/2)`.

It is kept visibly in this form rather than defined as a quotient by the
multiplicity factor. -/
def convexPlankFrostmanUnionLowerRHS
    (_D : ShadedConvexPlankFamily index a b)
    (epsilon beta : Real) (CF : ENNReal) (M : NNReal) : ENNReal :=
  (a : ENNReal) ^ epsilon *
    CF ^ (beta / 2 - 1) *
    (b : ENNReal) ^ (2 * beta) *
    (((M : ENNReal)⁻¹ *
      ((b : ENNReal) ^ (2 : Nat) *
        (Fintype.card index : ENNReal))) ^ (beta / 2))

/-- The exact union floor supplied by the low-average alternative before
the fixed constants and surplus powers of `a` are absorbed. -/
def lowAverageMultiplicityUnionFloor
    (D : ShadedConvexPlankFamily index a b) (eta : Real) : ENNReal :=
  ((a : ENNReal) ^ eta * familyVolume D.family) /
    (a : ENNReal) ^ (-eta)

/-- The exact volume envelope obtained by summing the upper volume bound
`volume P <= a*b` over the indexed plank family. -/
def convexPlankFamilyMassEnvelope
    (_D : ShadedConvexPlankFamily index a b) : ENNReal :=
  (Fintype.card index : ENNReal) * (a : ENNReal) * (b : ENNReal)

/-- The actual shading mass is bounded by the explicit plank mass envelope.
This uses the geometric `IsPlank` certificates stored in `D`, not a scalar
budget supplied by a caller. -/
theorem shadingMass_le_convexPlankFamilyMassEnvelope
    (D : ShadedConvexPlankFamily index a b) :
    D.shading.shadingMass <= convexPlankFamilyMassEnvelope D := by
  calc
    D.shading.shadingMass <= familyVolume D.family :=
      D.shading.shadingMass_le_familyVolume
    _ <= ∑ _i : index, (a : ENNReal) * (b : ENNReal) := by
      unfold familyVolume
      apply Finset.sum_le_sum
      intro i _hi
      exact (D.all_isPlank i).volume_upper_bound
    _ = convexPlankFamilyMassEnvelope D := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold convexPlankFamilyMassEnvelope
      ac_rfl

/-- Expansion of the paper's `(M⁻¹ S)^(beta/2)` term.  Only the
nonnegativity of the power is needed; this identity itself remains valid at
the endpoint values of `M` and `S`. -/
theorem inv_mul_rpow_halfBeta
    (M S : ENNReal) {beta : Real} (hbeta0 : 0 <= beta) :
    (M⁻¹ * S) ^ (beta / 2) =
      M ^ (-(beta / 2)) * S ^ (beta / 2) := by
  have hp : 0 <= beta / 2 := by linarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.inv_rpow,
    <- ENNReal.rpow_neg]

/-- The Family 6 multiplicity factor and the paper's union factor multiply
to the explicit total plank-volume envelope.  The assumptions on `CF` and
`M` are exactly the nondegenerate hypotheses needed to cancel opposite real
powers; the scale hypotheses make the same cancellation valid for `a` and
`b`. -/
theorem convexPlankFrostmanFactor_mul_unionLowerRHS
    (D : ShadedConvexPlankFamily index a b)
    (epsilon beta : Real) (CF : ENNReal) (M : NNReal)
    (ha : 0 < a) (hab : a <= b)
    (hCF0 : CF ≠ 0) (hCFTop : CF ≠ ∞) (hM : 0 < M)
    (hbeta0 : 0 <= beta) (hbeta2 : beta <= 2) :
    convexPlankFrostmanFactor D epsilon beta CF M *
        convexPlankFrostmanUnionLowerRHS D epsilon beta CF M =
      convexPlankFamilyMassEnvelope D := by
  have hb : 0 < b := ha.trans_le hab
  have ha0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  have haTop : (a : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hb0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb.ne'
  have hbTop : (b : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hM0 : (M : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hM.ne'
  have hMTop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hp : 0 <= beta / 2 := by linarith
  have hq : 0 <= 1 - beta / 2 := by linarith
  have hscaleCancel :
      (a : ENNReal) ^ (-epsilon) * (a : ENNReal) ^ epsilon = 1 := by
    rw [<- ENNReal.rpow_add (-epsilon) epsilon ha0 haTop]
    ring_nf
    simp
  have hCFCancel :
      CF ^ (1 - beta / 2) * CF ^ (beta / 2 - 1) = 1 := by
    rw [<- ENNReal.rpow_add (1 - beta / 2) (beta / 2 - 1)
      hCF0 hCFTop]
    ring_nf
    simp
  have hMCancel :
      (M : ENNReal) ^ (beta / 2) *
          (M : ENNReal) ^ (-(beta / 2)) = 1 := by
    rw [<- ENNReal.rpow_add (beta / 2) (-(beta / 2)) hM0 hMTop]
    ring_nf
    simp
  have hbCancel :
      (b : ENNReal) ^ (-2 * beta) *
          (b : ENNReal) ^ (2 * beta) = 1 := by
    rw [<- ENNReal.rpow_add (-2 * beta) (2 * beta) hb0 hbTop]
    ring_nf
    simp
  have hcountPower :
      (((b : ENNReal) ^ (2 : Nat) *
          (Fintype.card index : ENNReal)) ^ (1 - beta / 2)) *
        (((b : ENNReal) ^ (2 : Nat) *
          (Fintype.card index : ENNReal)) ^ (beta / 2)) =
        (b : ENNReal) ^ (2 : Nat) *
          (Fintype.card index : ENNReal) := by
    rw [<- ENNReal.rpow_add_of_nonneg
      (1 - beta / 2) (beta / 2) hq hp]
    ring_nf
    simp
  unfold convexPlankFrostmanFactor convexPlankFrostmanUnionLowerRHS
  rw [inv_mul_rpow_halfBeta (M : ENNReal)
    ((b : ENNReal) ^ (2 : Nat) * (Fintype.card index : ENNReal))
    hbeta0]
  calc
    ((a : ENNReal) ^ (-epsilon) *
          CF ^ (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat) *
            (Fintype.card index : ENNReal)) ^ (1 - beta / 2))) *
        ((a : ENNReal) ^ epsilon *
          CF ^ (beta / 2 - 1) *
          (b : ENNReal) ^ (2 * beta) *
          ((M : ENNReal) ^ (-(beta / 2)) *
            (((b : ENNReal) ^ (2 : Nat) *
              (Fintype.card index : ENNReal)) ^ (beta / 2)))) =
        ((a : ENNReal) ^ (-epsilon) * (a : ENNReal) ^ epsilon) *
          (CF ^ (1 - beta / 2) * CF ^ (beta / 2 - 1)) *
          ((M : ENNReal) ^ (beta / 2) *
            (M : ENNReal) ^ (-(beta / 2))) *
          ((b : ENNReal) ^ (-2 * beta) *
            (b : ENNReal) ^ (2 * beta)) *
          ((((b : ENNReal) ^ (2 : Nat) *
              (Fintype.card index : ENNReal)) ^ (1 - beta / 2)) *
            (((b : ENNReal) ^ (2 : Nat) *
              (Fintype.card index : ENNReal)) ^ (beta / 2))) *
          ((a : ENNReal) / (b : ENNReal)) := by
      ac_rfl
    _ = ((b : ENNReal) ^ (2 : Nat) *
          (Fintype.card index : ENNReal)) *
        ((a : ENNReal) / (b : ENNReal)) := by
      rw [hscaleCancel, hCFCancel, hMCancel, hbCancel, hcountPower]
      simp
    _ = convexPlankFamilyMassEnvelope D := by
      unfold convexPlankFamilyMassEnvelope
      rw [pow_two]
      rw [show (b : ENNReal) * (b : ENNReal) *
          (Fintype.card index : ENNReal) *
            ((a : ENNReal) / (b : ENNReal)) =
          ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) *
            ((Fintype.card index : ENNReal) * (b : ENNReal)) by ac_rfl]
      rw [ENNReal.div_mul_cancel hb0 hbTop]
      ac_rfl

/-- The final algebra in the paper's plank Frostman lemma: its literal
union-volume lower bound implies the exact Family 6 average-multiplicity
bound.  The required mass comparison is proved internally from the actual
`IsPlank` volume certificates.  Empty families are handled separately, so
the theorem does not impose an unnecessary global `Nonempty index` premise. -/
theorem averageMultiplicity_le_convexPlankFrostmanFactor_of_unionLower
    (D : ShadedConvexPlankFamily index a b)
    (epsilon beta : Real) (CF : ENNReal) (M : NNReal)
    (hCF0 : CF ≠ 0) (hCFTop : CF ≠ ∞) (hM : 0 < M)
    (hbeta0 : 0 <= beta) (hbeta2 : beta <= 2)
    (hunion :
      convexPlankFrostmanUnionLowerRHS D epsilon beta CF M <=
        volume D.shading.shadedUnion) :
    D.shading.averageMultiplicity <=
      convexPlankFrostmanFactor D epsilon beta CF M := by
  by_cases hindex : Nonempty index
  · let i0 : index := Classical.choice hindex
    have ha : 0 < a := (D.all_isPlank i0).1
    have hab : a <= b := (D.all_isPlank i0).2.1
    apply averageMultiplicity_le_of_shadingMass_le_rhs_mul_unionVolumeFloor
      D.shading hunion
    calc
      D.shading.shadingMass <= convexPlankFamilyMassEnvelope D :=
        shadingMass_le_convexPlankFamilyMassEnvelope D
      _ = convexPlankFrostmanFactor D epsilon beta CF M *
          convexPlankFrostmanUnionLowerRHS D epsilon beta CF M :=
        (convexPlankFrostmanFactor_mul_unionLowerRHS
          D epsilon beta CF M ha hab hCF0 hCFTop hM hbeta0 hbeta2).symm
  · let _ : IsEmpty index := ⟨fun i => hindex ⟨i⟩⟩
    simp [Shading.averageMultiplicity, Shading.shadingMass,
      Shading.shadedUnion]

/-- Density and `averageMultiplicity <= a^(-eta)` give the exact low-branch
union floor.  The imported division-free average-to-union lemma handles all
zero and infinite endpoint cases, so no scale side condition is needed. -/
theorem lowAverageMultiplicityUnionFloor_le_shadedUnion
    (D : ShadedConvexPlankFamily index a b) (eta : Real)
    (hdensity :
      (a : ENNReal) ^ eta <= D.shading.shadingDensity)
    (hlow :
      D.shading.averageMultiplicity <= (a : ENNReal) ^ (-eta)) :
    lowAverageMultiplicityUnionFloor D eta <=
      volume D.shading.shadedUnion := by
  have hmass :
      (a : ENNReal) ^ eta * familyVolume D.family <=
        D.shading.shadingMass := by
    calc
      (a : ENNReal) ^ eta * familyVolume D.family <=
          D.shading.shadingDensity * familyVolume D.family := by
        gcongr
      _ = D.shading.shadingMass :=
        shadingDensity_mul_familyVolume D.shading
  exact massFloor_div_cap_le_volume_shadedUnion_of_averageMultiplicity_le
    D.shading
    ((a : ENNReal) ^ eta * familyVolume D.family)
    ((a : ENNReal) ^ (-eta)) hmass hlow

/-- The literal paper union bound in the low-average branch.  The sole extra
premise is the scalar absorption which says that the surplus epsilon power
and fixed geometric constants put the paper right-hand side below the exact
low-branch floor.  It contains no multiplicity or union conclusion supplied
as an assumption. -/
theorem convexPlankFrostmanUnionLowerRHS_le_of_lowAverageMultiplicity
    (D : ShadedConvexPlankFamily index a b)
    (epsilon beta eta : Real) (CF : ENNReal) (M : NNReal)
    (hdensity :
      (a : ENNReal) ^ eta <= D.shading.shadingDensity)
    (hlow :
      D.shading.averageMultiplicity <= (a : ENNReal) ^ (-eta))
    (habsorb :
      convexPlankFrostmanUnionLowerRHS D epsilon beta CF M <=
        lowAverageMultiplicityUnionFloor D eta) :
    convexPlankFrostmanUnionLowerRHS D epsilon beta CF M <=
      volume D.shading.shadedUnion :=
  habsorb.trans
    (lowAverageMultiplicityUnionFloor_le_shadedUnion D eta hdensity hlow)

#print axioms lowAverageMultiplicityUnionFloor_le_shadedUnion
#print axioms
  convexPlankFrostmanUnionLowerRHS_le_of_lowAverageMultiplicity
#print axioms shadingMass_le_convexPlankFamilyMassEnvelope
#print axioms inv_mul_rpow_halfBeta
#print axioms convexPlankFrostmanFactor_mul_unionLowerRHS
#print axioms
  averageMultiplicity_le_convexPlankFrostmanFactor_of_unionLower

end
end Family8PlankFrostmanLowAverageFinalAlgebraV1
