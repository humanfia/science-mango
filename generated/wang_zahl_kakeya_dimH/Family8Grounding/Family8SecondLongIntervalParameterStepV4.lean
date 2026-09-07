import Mathlib

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SecondLongIntervalParameterStepV4

noncomputable section

/-!
# An explicit parameter step for the second long interval

For Main Lemma 2, this file makes the backwards choice behind
`etaPrime = 12 eta / (epsilon beta)` explicit and proves the exact
multiplicative absorption of the outer and inner estimates.
-/

def secondLongEtaPrime (epsilon beta eta : Real) : Real :=
  12 * eta / (epsilon * beta)

def secondLongEtaChoice
    (epsilon beta nextEta gain : Real) : Real :=
  min (nextEta / 2)
    (min (epsilon ^ 2 * beta * nextEta / 24)
      (epsilon * beta * gain / 100))

theorem secondLongEtaChoice_pos
    {epsilon beta nextEta gain : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hnext : 0 < nextEta) (hgain : 0 < gain) :
    0 < secondLongEtaChoice epsilon beta nextEta gain := by
  simp only [secondLongEtaChoice, lt_min_iff]
  constructor
  · positivity
  constructor <;> positivity

theorem secondLongEtaChoice_lt_next
    {epsilon beta nextEta gain : Real}
    (hnext : 0 < nextEta) :
    secondLongEtaChoice epsilon beta nextEta gain < nextEta := by
  have hhalf : nextEta / 2 < nextEta := by linarith
  exact (min_le_left _ _).trans_lt hhalf

theorem secondLongEtaChoice_le_scaleTerm
    (epsilon beta nextEta gain : Real) :
    secondLongEtaChoice epsilon beta nextEta gain <=
      epsilon ^ 2 * beta * nextEta / 24 := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem secondLongEtaChoice_le_gainTerm
    (epsilon beta nextEta gain : Real) :
    secondLongEtaChoice epsilon beta nextEta gain <=
      epsilon * beta * gain / 100 := by
  exact (min_le_right _ _).trans (min_le_right _ _)

theorem secondLongEtaPrime_le_half_epsilon_mul_next
    {epsilon beta nextEta gain : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) :
    secondLongEtaPrime epsilon beta
        (secondLongEtaChoice epsilon beta nextEta gain) <=
      epsilon * nextEta / 2 := by
  have hdenom : 0 < epsilon * beta := mul_pos hepsilon hbeta
  rw [secondLongEtaPrime]
  apply (div_le_iff₀ hdenom).2
  have hchoice := secondLongEtaChoice_le_scaleTerm
    epsilon beta nextEta gain
  have hmul := mul_le_mul_of_nonneg_left hchoice
    (by norm_num : (0 : Real) <= 12)
  calc
    12 * secondLongEtaChoice epsilon beta nextEta gain <=
        12 * (epsilon ^ 2 * beta * nextEta / 24) := hmul
    _ = (epsilon * nextEta / 2) * (epsilon * beta) := by ring

theorem secondLong_loss_le_half_gain
    {epsilon beta nextEta gain : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetaOne : beta <= 1) (hnext : 0 < nextEta) (hgain : 0 < gain) :
    2 * secondLongEtaPrime epsilon beta
          (secondLongEtaChoice epsilon beta nextEta gain) +
        10 * secondLongEtaChoice epsilon beta nextEta gain / epsilon <=
      gain / 2 := by
  let eta := secondLongEtaChoice epsilon beta nextEta gain
  have hdenom : 0 < epsilon * beta := mul_pos hepsilon hbeta
  have hchoice : eta <= epsilon * beta * gain / 100 := by
    exact secondLongEtaChoice_le_gainTerm epsilon beta nextEta gain
  have heta0 : 0 <= eta :=
    (secondLongEtaChoice_pos hepsilon hbeta hnext hgain).le
  have hcoeff0 : 0 <= 24 + 10 * beta := by positivity
  have hcoeff : 24 + 10 * beta <= 34 := by linarith
  have hbound0 : 0 <= epsilon * beta * gain / 100 := by positivity
  have hproduct : eta * (24 + 10 * beta) <=
      (epsilon * beta * gain / 100) * 34 := by
    exact mul_le_mul hchoice hcoeff hcoeff0 hbound0
  have hbase0 : 0 <= epsilon * beta * gain := by positivity
  have hrhs : (epsilon * beta * gain / 100) * 34 <=
      (gain / 2) * (epsilon * beta) := by
    calc
      (epsilon * beta * gain / 100) * 34 =
          (34 / 100 : Real) * (epsilon * beta * gain) := by ring
      _ <= (1 / 2 : Real) * (epsilon * beta * gain) :=
        mul_le_mul_of_nonneg_right (by norm_num) hbase0
      _ = (gain / 2) * (epsilon * beta) := by ring
  have hscaled :
      (2 * secondLongEtaPrime epsilon beta eta + 10 * eta / epsilon) *
          (epsilon * beta) <= (gain / 2) * (epsilon * beta) := by
    calc
      (2 * secondLongEtaPrime epsilon beta eta + 10 * eta / epsilon) *
            (epsilon * beta) = eta * (24 + 10 * beta) := by
        dsimp only [secondLongEtaPrime]
        field_simp [hepsilon.ne', hbeta.ne']
        ring
      _ <= (epsilon * beta * gain / 100) * 34 := hproduct
      _ <= (gain / 2) * (epsilon * beta) := hrhs
  exact le_of_mul_le_mul_right hscaled hdenom

theorem secondLong_requested_gain_le_net_gain
    {epsilon beta nextEta gain : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetaOne : beta <= 1) (hnext : 0 < nextEta) (hgain : 0 < gain) :
    10 * secondLongEtaChoice epsilon beta nextEta gain / epsilon <=
      gain - 2 * secondLongEtaPrime epsilon beta
        (secondLongEtaChoice epsilon beta nextEta gain) := by
  have h := secondLong_loss_le_half_gain
    (nextEta := nextEta) hepsilon hbeta hbetaOne hnext hgain
  linarith

theorem secondLong_mul_absorption
    {d : NNReal} {epsilon beta nextEta gain : Real}
    {outer inner whole outerCard innerCard totalCard : ENNReal}
    (hd : 0 < d) (hdOne : d <= 1)
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetaOne : beta <= 1) (hnext : 0 < nextEta) (hgain : 0 < gain)
    (hwhole : whole <= outer * inner)
    (houter : outer <=
      (d : ENNReal) ^
          (-2 * secondLongEtaPrime epsilon beta
            (secondLongEtaChoice epsilon beta nextEta gain)) * outerCard)
    (hinner : inner <= (d : ENNReal) ^ gain * innerCard)
    (hcards : outerCard * innerCard <= totalCard) :
    whole <=
      (d : ENNReal) ^
          (10 * secondLongEtaChoice epsilon beta nextEta gain / epsilon) *
        totalCard := by
  let eta := secondLongEtaChoice epsilon beta nextEta gain
  let etaPrime := secondLongEtaPrime epsilon beta eta
  have hd0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : (d : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hdOneENN : (d : ENNReal) <= 1 := by exact_mod_cast hdOne
  have hnet : 10 * eta / epsilon <= gain - 2 * etaPrime := by
    exact secondLong_requested_gain_le_net_gain
      hepsilon hbeta hbetaOne hnext hgain
  have hpower :
      (d : ENNReal) ^ (gain - 2 * etaPrime) <=
        (d : ENNReal) ^ (10 * eta / epsilon) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN hnet
  calc
    whole <= outer * inner := hwhole
    _ <= (((d : ENNReal) ^ (-2 * etaPrime)) * outerCard) *
        (((d : ENNReal) ^ gain) * innerCard) :=
      mul_le_mul' houter hinner
    _ = ((d : ENNReal) ^ (-2 * etaPrime) *
          (d : ENNReal) ^ gain) * (outerCard * innerCard) := by
      ring
    _ = (d : ENNReal) ^ (-2 * etaPrime + gain) *
        (outerCard * innerCard) := by
      exact congrArg (fun z : ENNReal => z * (outerCard * innerCard))
        (ENNReal.rpow_add _ _ hd0 hdTop).symm
    _ = (d : ENNReal) ^ (gain - 2 * etaPrime) *
        (outerCard * innerCard) := by
      congr 2
      ring
    _ <= (d : ENNReal) ^ (10 * eta / epsilon) *
        (outerCard * innerCard) := mul_le_mul' hpower le_rfl
    _ <= (d : ENNReal) ^ (10 * eta / epsilon) * totalCard :=
      mul_le_mul' le_rfl hcards

#print axioms secondLongEtaChoice_pos
#print axioms secondLongEtaPrime_le_half_epsilon_mul_next
#print axioms secondLong_loss_le_half_gain
#print axioms secondLong_requested_gain_le_net_gain
#print axioms secondLong_mul_absorption

end

end Family8SecondLongIntervalParameterStepV4
