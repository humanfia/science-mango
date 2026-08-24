import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32JetSeparationV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32LocalTangencyV1

open FamilyStickyCinematicL32JetSeparationV1

/-!
# Local value--slope--curvature alternatives for cinematic traces

Provenance: the short-interval alternative in Pramanik--Yang--Zahl,
*A Furstenberg-type problem for circles, and a Kaufman-type restricted
projection theorem in R^3*, arXiv:2207.02259v3, Lemma 3.5, combined with
the explicit Wang--Zahl cinematic family from their Lemma 7.3.

The module proves the local alternative from an oscillation estimate and
the already verified pointwise jet separation.  In particular, simultaneous
near intersection and near tangency force quantitative curvature separation.
No incidence bound, lens-counting proposition, maximal estimate, or
projection lower bound is assumed.
-/

/-- The `l1` distance between two coefficient triples. -/
def coefficientDistance (da db dd : Real) : Real :=
  |da| + |db| + |dd|

/-- A value and slope jet are simultaneously small at one parameter. -/
def NearTangentAt (eta : Real)
    (da db dd ft f1 t : Real) : Prop :=
  |traceJet0 da db dd ft t| <= eta ∧
    |traceJet1 db dd ft f1 t| <= eta

/-- A purely local small-or-large alternative.  If a scalar function
oscillates by less than `r` on a set, then either it is everywhere below
`2r`, or it is everywhere at least `r`.  This is the metric core of PYZ
Lemma 3.5. -/
theorem small_or_large_of_local_oscillation
    {iota : Type*} (I : Set iota) (k : iota -> Real) (r : Real)
    (hosc : forall x, x ∈ I -> forall y, y ∈ I -> |k x - k y| < r) :
    (forall x, x ∈ I -> |k x| < 2 * r) ∨
      (forall x, x ∈ I -> r <= |k x|) := by
  by_cases hsmall : ∃ x ∈ I, |k x| < r
  · left
    obtain ⟨x, hxI, hx⟩ := hsmall
    intro y hyI
    calc
      |k y| = |(k y - k x) + k x| := by ring_nf
      _ <= |k y - k x| + |k x| := abs_add_le _ _
      _ < r + r := add_lt_add (hosc y hyI x hxI) hx
      _ = 2 * r := by ring_nf
  · right
    intro x hxI
    exact le_of_not_gt (fun hx => hsmall ⟨x, hxI, hx⟩)

/-- Pointwise near tangency forces the second jets apart.  The constants are
chosen with slack for later short-interval arguments. -/
theorem nearTangentAt_forces_curvature_separation
    (da db dd ft f1 f2 t eta : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2)
    (hf1Lower : 1 <= |f1|) (hf1Upper : |f1| <= 2)
    (hf2 : |f2| <= 1 / 100)
    (heta : eta <= coefficientDistance da db dd / 800)
    (hnear : NearTangentAt eta da db dd ft f1 t) :
    coefficientDistance da db dd / 400 <=
      |traceJet2 db dd f1 f2 t| := by
  have hsep := cinematic_trace_jet_separation
    da db dd ft f1 f2 t ht hft hf1Lower hf1Upper hf2
  rw [coefficientDistance] at heta ⊢
  rcases hnear with ⟨hvalue, hslope⟩
  nlinarith

/-- Strict form used after the small branch of the local dichotomy. -/
theorem small_value_and_slope_force_curvature
    (da db dd ft f1 f2 t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2)
    (hf1Lower : 1 <= |f1|) (hf1Upper : |f1| <= 2)
    (hf2 : |f2| <= 1 / 100)
    (hvalue : |traceJet0 da db dd ft t| <
      coefficientDistance da db dd / 600)
    (hslope : |traceJet1 db dd ft f1 t| <
      coefficientDistance da db dd / 600) :
    coefficientDistance da db dd / 600 <
      |traceJet2 db dd f1 f2 t| := by
  have hsep := cinematic_trace_jet_separation
    da db dd ft f1 f2 t ht hft hf1Lower hf1Upper hf2
  rw [coefficientDistance] at hvalue hslope ⊢
  nlinarith

/-- Short-interval cinematic trichotomy for the explicit Wang--Zahl trace.
On a set where the value and slope jets each oscillate by less than
`coefficientDistance / 1200`, either the values are uniformly separated,
the slopes are uniformly separated, or the curvatures are uniformly
separated. -/
theorem local_value_slope_curvature_trichotomy
    {iota : Type*} (I : Set iota)
    (da db dd : Real) (ft f1 f2 parameter : iota -> Real)
    (hparameter : forall theta, theta ∈ I -> |parameter theta| <= 1)
    (hft : forall theta, theta ∈ I -> |ft theta| <= 2)
    (hf1Lower : forall theta, theta ∈ I -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ I -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ I -> |f2 theta| <= 1 / 100)
    (hosc0 : forall x, x ∈ I -> forall y, y ∈ I ->
      |traceJet0 da db dd (ft x) (parameter x) -
        traceJet0 da db dd (ft y) (parameter y)| <
          coefficientDistance da db dd / 1200)
    (hosc1 : forall x, x ∈ I -> forall y, y ∈ I ->
      |traceJet1 db dd (ft x) (f1 x) (parameter x) -
        traceJet1 db dd (ft y) (f1 y) (parameter y)| <
          coefficientDistance da db dd / 1200) :
    (forall theta, theta ∈ I -> coefficientDistance da db dd / 1200 <=
      |traceJet0 da db dd (ft theta) (parameter theta)|) ∨
    (forall theta, theta ∈ I -> coefficientDistance da db dd / 1200 <=
      |traceJet1 db dd (ft theta) (f1 theta) (parameter theta)|) ∨
    (forall theta, theta ∈ I -> coefficientDistance da db dd / 600 <
      |traceJet2 db dd (f1 theta) (f2 theta) (parameter theta)|) := by
  rcases small_or_large_of_local_oscillation I
      (fun theta => traceJet0 da db dd (ft theta) (parameter theta))
      (coefficientDistance da db dd / 1200) hosc0 with hsmall0 | hlarge0
  · rcases small_or_large_of_local_oscillation I
        (fun theta => traceJet1 db dd (ft theta) (f1 theta) (parameter theta))
        (coefficientDistance da db dd / 1200) hosc1 with hsmall1 | hlarge1
    · right
      right
      intro theta htheta
      apply small_value_and_slope_force_curvature
        da db dd (ft theta) (f1 theta) (f2 theta) (parameter theta)
        (hparameter theta htheta) (hft theta htheta)
        (hf1Lower theta htheta) (hf1Upper theta htheta)
        (hf2 theta htheta)
      · nlinarith [hsmall0 theta htheta]
      · nlinarith [hsmall1 theta htheta]
    · exact Or.inr (Or.inl hlarge1)
  · exact Or.inl hlarge0

#print axioms small_or_large_of_local_oscillation
#print axioms nearTangentAt_forces_curvature_separation
#print axioms small_value_and_slope_force_curvature
#print axioms local_value_slope_curvature_trichotomy

end FamilyStickyCinematicL32LocalTangencyV1
