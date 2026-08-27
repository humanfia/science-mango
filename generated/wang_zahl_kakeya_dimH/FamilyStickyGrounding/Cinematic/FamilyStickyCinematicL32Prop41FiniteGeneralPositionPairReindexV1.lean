import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ActualTubeConstantShiftV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Finite general-position perturbations and retained-pair reindexing

The infinitesimal perturbation in PYZ Proposition 4.1 has two logically
separate parts.  This module makes both finite pieces explicit.

For A2--A3, curve `c` is moved vertically by `epsilon * weight c`.  Endpoint
collisions exclude two scalar parameters per ordered curve pair.  A
tangential collision excludes the quotient of one *critical height
difference* by the nonzero weight difference.  Consequently a finite curve
family has only finitely many bad perturbation parameters as soon as each
pair has finitely many critical height differences.  This is strictly weaker
than assuming A3: the theorem constructs A3 after choosing one parameter
outside the finite bad set.

The final section constructs the literal unordered `FirstGenerationCurvePair`
attached to every retained rectangle and proves exact cardinality retention
under the sole necessary bookkeeping input that distinct retained rectangles
have distinct unordered tube pairs.
-/

/-- Vertical perturbation of an abstract graph family.  Its first derivative
is unchanged, which is why a tangential collision is controlled by a scalar
critical height difference. -/
def verticallyPerturbedGraph {curve : Type*}
    (graph : curve -> Real -> Real) (weight : curve -> Real)
    (epsilon : Real) (c : curve) (theta : Real) : Real :=
  graph c theta + epsilon * weight c

/-- Height differences attained at parameters where two first derivatives
agree.  Finiteness of this set is the exact residual geometric input used to
produce A3. -/
def criticalHeightDifferenceSet {curve : Type*}
    (graph first : curve -> Real -> Real) (A B : Real)
    (c d : curve) : Set Real :=
  {v | exists theta, theta ∈ Icc A B ∧
    first c theta = first d theta ∧
    v = graph d theta - graph c theta}

/-- The two endpoint collisions and all tangential collisions forbidden for
one ordered pair. -/
def pairGeneralPositionBadParameters {curve : Type*}
    (graph first : curve -> Real -> Real) (weight : curve -> Real)
    (A B : Real) (c d : curve) : Set Real :=
  {((graph d A - graph c A) / (weight c - weight d)),
      ((graph d B - graph c B) / (weight c - weight d))} ∪
    ((fun v => v / (weight c - weight d)) ''
      criticalHeightDifferenceSet graph first A B c d)

/-- The global finite-family bad set.  Including diagonal pairs is harmless
and simplifies the finite-union construction. -/
def familyGeneralPositionBadParameters
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (graph first : curve -> Real -> Real) (weight : curve -> Real)
    (A B : Real) : Set Real :=
  ⋃ c ∈ (curves : Set curve), ⋃ d ∈ (curves : Set curve),
    pairGeneralPositionBadParameters graph first weight A B c d

/-- A diagonal critical-height set is contained in `{0}`, even when the
parameter interval is empty. -/
theorem criticalHeightDifferenceSet_self_finite
    {curve : Type*} (graph first : curve -> Real -> Real)
    (A B : Real) (c : curve) :
    (criticalHeightDifferenceSet graph first A B c c).Finite := by
  apply (Set.finite_singleton (0 : Real)).subset
  rintro v ⟨theta, _htheta, _hfirst, hv⟩
  simp only [sub_self] at hv
  simpa only [hv] using (Set.mem_singleton (0 : Real))

/-- The bad set of one pair is finite whenever its critical-height set is
finite. -/
theorem pairGeneralPositionBadParameters_finite
    {curve : Type*} (graph first : curve -> Real -> Real)
    (weight : curve -> Real) (A B : Real) (c d : curve)
    (hcritical : (criticalHeightDifferenceSet graph first A B c d).Finite) :
    (pairGeneralPositionBadParameters graph first weight A B c d).Finite := by
  exact (Set.toFinite {_ , _}).union (hcritical.image _)

/-- Finite union over a finite curve family.  Only distinct-pair critical
height finiteness is requested; the diagonal case was proved above. -/
theorem familyGeneralPositionBadParameters_finite
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (graph first : curve -> Real -> Real) (weight : curve -> Real)
    (A B : Real)
    (hcritical : forall c, c ∈ curves -> forall d, d ∈ curves -> c ≠ d ->
      (criticalHeightDifferenceSet graph first A B c d).Finite) :
    (familyGeneralPositionBadParameters curves graph first weight A B).Finite := by
  rw [familyGeneralPositionBadParameters]
  refine curves.finite_toSet.biUnion ?_
  intro c hc
  refine curves.finite_toSet.biUnion ?_
  intro d hd
  apply pairGeneralPositionBadParameters_finite
  by_cases hcd : c = d
  · subst d
    exact criticalHeightDifferenceSet_self_finite graph first A B c
  · exact hcritical c hc d hd hcd

/-- An endpoint equality for a distinct weighted pair puts the perturbation
parameter in the explicit pair bad set. -/
theorem mem_pairBad_of_endpoint_collision
    {curve : Type*} {graph first : curve -> Real -> Real}
    {weight : curve -> Real} {A B epsilon : Real} {c d : curve}
    (hweight : weight c ≠ weight d) (theta : Real)
    (htheta : theta = A ∨ theta = B)
    (heq : verticallyPerturbedGraph graph weight epsilon c theta =
      verticallyPerturbedGraph graph weight epsilon d theta) :
    epsilon ∈ pairGeneralPositionBadParameters
      graph first weight A B c d := by
  have hden : weight c - weight d ≠ 0 := sub_ne_zero.mpr hweight
  have hepsilon : epsilon =
      (graph d theta - graph c theta) / (weight c - weight d) := by
    apply (eq_div_iff hden).2
    simp only [verticallyPerturbedGraph] at heq
    linarith
  rcases htheta with rfl | rfl
  · exact Or.inl (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      hepsilon, true_or])
  · exact Or.inl (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      hepsilon, or_true])

/-- A simultaneous value/first-derivative collision puts the perturbation
parameter in the critical-value part of the pair bad set. -/
theorem mem_pairBad_of_tangential_collision
    {curve : Type*} {graph first : curve -> Real -> Real}
    {weight : curve -> Real} {A B epsilon theta : Real} {c d : curve}
    (hweight : weight c ≠ weight d) (htheta : theta ∈ Icc A B)
    (hvalue : verticallyPerturbedGraph graph weight epsilon c theta =
      verticallyPerturbedGraph graph weight epsilon d theta)
    (hfirst : first c theta = first d theta) :
    epsilon ∈ pairGeneralPositionBadParameters
      graph first weight A B c d := by
  have hden : weight c - weight d ≠ 0 := sub_ne_zero.mpr hweight
  have hepsilon : epsilon =
      (graph d theta - graph c theta) / (weight c - weight d) := by
    apply (eq_div_iff hden).2
    simp only [verticallyPerturbedGraph] at hvalue
    linarith
  apply Or.inr
  refine ⟨graph d theta - graph c theta, ?_, hepsilon.symm⟩
  exact ⟨theta, htheta, hfirst, rfl⟩

/-- A local pair bad parameter belongs to the global family bad set. -/
theorem pairBad_subset_familyBad
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {graph first : curve -> Real -> Real} {weight : curve -> Real}
    {A B : Real} {c d : curve} (hc : c ∈ curves) (hd : d ∈ curves) :
    pairGeneralPositionBadParameters graph first weight A B c d ⊆
      familyGeneralPositionBadParameters curves graph first weight A B := by
  intro epsilon hepsilon
  rw [familyGeneralPositionBadParameters]
  exact Set.mem_iUnion_of_mem c <| Set.mem_iUnion_of_mem hc <|
    Set.mem_iUnion_of_mem d <| Set.mem_iUnion_of_mem hd hepsilon

/-- Outside the explicit global bad set, the vertical perturbation satisfies
both paper assumptions A2 and A3. -/
theorem generalPosition_of_not_mem_familyBad
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (graph first : curve -> Real -> Real) (weight : curve -> Real)
    (A B epsilon : Real)
    (hweight : Set.InjOn weight (curves : Set curve))
    (hepsilon : epsilon ∉
      familyGeneralPositionBadParameters curves graph first weight A B) :
    EndpointValuesDistinct curves
        (verticallyPerturbedGraph graph weight epsilon) A B ∧
      NoTangentialGraphIntersections curves
        (verticallyPerturbedGraph graph weight epsilon) first A B := by
  constructor
  · constructor
    · intro c hc d hd heq
      by_contra hcd
      have hw : weight c ≠ weight d := fun heqWeight =>
        hcd (hweight hc hd heqWeight)
      exact hepsilon (pairBad_subset_familyBad hc hd
        (mem_pairBad_of_endpoint_collision hw A (Or.inl rfl) heq))
    · intro c hc d hd heq
      by_contra hcd
      have hw : weight c ≠ weight d := fun heqWeight =>
        hcd (hweight hc hd heqWeight)
      exact hepsilon (pairBad_subset_familyBad hc hd
        (mem_pairBad_of_endpoint_collision hw B (Or.inr rfl) heq))
  · intro c hc d hd hcd theta htheta hcollision
    exact hepsilon (pairBad_subset_familyBad hc hd
      (mem_pairBad_of_tangential_collision
        (fun heqWeight => hcd (hweight hc hd heqWeight))
        htheta hcollision.1 hcollision.2))

/-- Arbitrarily small *positive* general-position parameters exist.  This is
the formal finite-bad-parameter form of the paper's word “infinitesimal”. -/
theorem exists_small_positive_generalPositionParameter
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (graph first : curve -> Real -> Real) (weight : curve -> Real)
    (A B tolerance : Real) (htolerance : 0 < tolerance)
    (hweight : Set.InjOn weight (curves : Set curve))
    (hcritical : forall c, c ∈ curves -> forall d, d ∈ curves -> c ≠ d ->
      (criticalHeightDifferenceSet graph first A B c d).Finite) :
    exists epsilon, 0 < epsilon ∧ epsilon < tolerance ∧
      EndpointValuesDistinct curves
        (verticallyPerturbedGraph graph weight epsilon) A B ∧
      NoTangentialGraphIntersections curves
        (verticallyPerturbedGraph graph weight epsilon) first A B := by
  let bad := familyGeneralPositionBadParameters
    curves graph first weight A B
  have hbad : bad.Finite :=
    familyGeneralPositionBadParameters_finite curves graph first weight A B
      hcritical
  have hnotSubset : ¬ Ioo (0 : Real) tolerance ⊆ bad := by
    intro hsubset
    exact (Set.Ioo_infinite htolerance).not_finite (hbad.subset hsubset)
  rw [Set.not_subset] at hnotSubset
  obtain ⟨epsilon, hepsilon, hepsilonBad⟩ := hnotSubset
  obtain ⟨hpositive, hsmall⟩ := hepsilon
  obtain ⟨hA2, hA3⟩ := generalPosition_of_not_mem_familyBad
    curves graph first weight A B epsilon hweight hepsilonBad
  exact ⟨epsilon, hpositive, hsmall, hA2, hA3⟩

/-! ## Realization by actual tube translations -/

/-- Apply the curve-dependent vertical perturbation by an honest Euclidean
translation of each actual tube. -/
def individuallyTracePerturbedTube {radius : NNReal}
    (weight : Tube radius -> Real) (epsilon : Real) (T : Tube radius) :
    Tube radius :=
  traceTranslateTube T (epsilon * weight T)

/-- The finite actual tube family after curve-dependent perturbation. -/
def individuallyTracePerturbedTubeFamily {radius : NNReal}
    (curves : Finset (Tube radius)) (weight : Tube radius -> Real)
    (epsilon : Real) : Finset (Tube radius) :=
  curves.image (individuallyTracePerturbedTube weight epsilon)

@[simp] theorem actualTubeGraph_individuallyTracePerturbedTube
    {radius : NNReal} (weight : Tube radius -> Real) (epsilon : Real)
    (T : Tube radius) (f : Real -> Real) (theta : Real) :
    actualTubeGraph (individuallyTracePerturbedTube weight epsilon T) f theta =
      verticallyPerturbedGraph (fun V => actualTubeGraph V f)
        weight epsilon T theta := by
  change cinematicTraceValue f
      (tubeGraphA (traceTranslateTube T (epsilon * weight T)))
      (tubeGraphB (traceTranslateTube T (epsilon * weight T)))
      (tubeGraphC (traceTranslateTube T (epsilon * weight T)))
      (tubeGraphD (traceTranslateTube T (epsilon * weight T))) theta =
    cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
      (tubeGraphC T) (tubeGraphD T) theta + epsilon * weight T
  exact cinematicTraceValue_traceTranslateTube
    T (epsilon * weight T) f theta

@[simp] theorem actualTubeGraphFirst_individuallyTracePerturbedTube
    {radius : NNReal} (weight : Tube radius -> Real) (epsilon : Real)
    (T : Tube radius) (f f1 : Real -> Real) (theta : Real) :
    actualTubeGraphFirst
        (individuallyTracePerturbedTube weight epsilon T) f f1 theta =
      actualTubeGraphFirst T f f1 theta := by
  change cinematicTraceFirstValue f f1
      (tubeGraphB (traceTranslateTube T (epsilon * weight T)))
      (tubeGraphC (traceTranslateTube T (epsilon * weight T)))
      (tubeGraphD (traceTranslateTube T (epsilon * weight T))) theta =
    cinematicTraceFirstValue f f1
      (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta
  simp only [tubeGraphB_traceTranslateTube, tubeGraphC_traceTranslateTube,
    tubeGraphD_traceTranslateTube]

/-- The abstract finite-bad-parameter theorem is realized by literal actual
tubes.  Besides A2--A3, the output records that the perturbation is injective
on the input family and hence preserves its exact cardinality. -/
theorem exists_small_positive_actualTubeGeneralPosition
    {radius : NNReal} (curves : Finset (Tube radius))
    (weight : Tube radius -> Real) (f f1 : Real -> Real)
    (A B tolerance : Real) (htolerance : 0 < tolerance)
    (hweight : Set.InjOn weight (curves : Set (Tube radius)))
    (hcritical : forall T, T ∈ curves -> forall U, U ∈ curves -> T ≠ U ->
      (criticalHeightDifferenceSet
        (fun V => actualTubeGraph V f)
        (fun V => actualTubeGraphFirst V f f1) A B T U).Finite) :
    exists epsilon, 0 < epsilon ∧ epsilon < tolerance ∧
      Set.InjOn (individuallyTracePerturbedTube weight epsilon)
        (curves : Set (Tube radius)) ∧
      (individuallyTracePerturbedTubeFamily curves weight epsilon).card =
        curves.card ∧
      EndpointValuesDistinct
        (individuallyTracePerturbedTubeFamily curves weight epsilon)
        (fun V => actualTubeGraph V f) A B ∧
      NoTangentialGraphIntersections
        (individuallyTracePerturbedTubeFamily curves weight epsilon)
        (fun V => actualTubeGraph V f)
        (fun V => actualTubeGraphFirst V f f1) A B := by
  obtain ⟨epsilon, hepsilonPos, hepsilonSmall, hA2Index, hA3Index⟩ :=
    exists_small_positive_generalPositionParameter curves
      (fun V => actualTubeGraph V f)
      (fun V => actualTubeGraphFirst V f f1) weight A B tolerance
      htolerance hweight hcritical
  have hinjective : Set.InjOn
      (individuallyTracePerturbedTube weight epsilon)
      (curves : Set (Tube radius)) := by
    intro T hT U hU hshift
    apply hA2Index.1 hT hU
    have hgraph := congrArg (fun V => actualTubeGraph V f A) hshift
    simpa only [actualTubeGraph_individuallyTracePerturbedTube] using hgraph
  have hcard :
      (individuallyTracePerturbedTubeFamily curves weight epsilon).card =
        curves.card := by
    exact Finset.card_image_of_injOn hinjective
  have hA2Actual : EndpointValuesDistinct
      (individuallyTracePerturbedTubeFamily curves weight epsilon)
      (fun V => actualTubeGraph V f) A B := by
    constructor
    · intro V hV W hW heq
      change V ∈ individuallyTracePerturbedTubeFamily curves weight epsilon at hV
      change W ∈ individuallyTracePerturbedTubeFamily curves weight epsilon at hW
      rw [individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV hW
      obtain ⟨T, hT, rfl⟩ := hV
      obtain ⟨U, hU, rfl⟩ := hW
      have hTU := hA2Index.1 hT hU (by
        simpa only [actualTubeGraph_individuallyTracePerturbedTube]
          using heq)
      rw [hTU]
    · intro V hV W hW heq
      change V ∈ individuallyTracePerturbedTubeFamily curves weight epsilon at hV
      change W ∈ individuallyTracePerturbedTubeFamily curves weight epsilon at hW
      rw [individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV hW
      obtain ⟨T, hT, rfl⟩ := hV
      obtain ⟨U, hU, rfl⟩ := hW
      have hTU := hA2Index.2 hT hU (by
        simpa only [actualTubeGraph_individuallyTracePerturbedTube]
          using heq)
      rw [hTU]
  have hA3Actual : NoTangentialGraphIntersections
      (individuallyTracePerturbedTubeFamily curves weight epsilon)
      (fun V => actualTubeGraph V f)
      (fun V => actualTubeGraphFirst V f f1) A B := by
    intro V hV W hW hVW theta htheta hcollision
    change V ∈ individuallyTracePerturbedTubeFamily curves weight epsilon at hV
    change W ∈ individuallyTracePerturbedTubeFamily curves weight epsilon at hW
    rw [individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV hW
    obtain ⟨T, hT, rfl⟩ := hV
    obtain ⟨U, hU, rfl⟩ := hW
    have hTU : T ≠ U := fun h => hVW (by rw [h])
    apply hA3Index T hT U hU hTU theta htheta
    constructor
    · simpa only [actualTubeGraph_individuallyTracePerturbedTube]
        using hcollision.1
    · simpa only [actualTubeGraphFirst_individuallyTracePerturbedTube]
        using hcollision.2
  exact ⟨epsilon, hepsilonPos, hepsilonSmall, hinjective, hcard,
    hA2Actual, hA3Actual⟩

/-! ## Retained rectangles as endpoint unordered-pair items -/

/-- The exact finite actual-tube family occurring in retained pairs. -/
def retainedPairTubeFamily
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius) :
    Finset (Tube radius) :=
  fiber.image T ∪ fiber.image U

theorem retainedPair_first_mem
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (i : alpha) (hi : i ∈ fiber) :
    T i ∈ retainedPairTubeFamily fiber T U := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem retainedPair_second_mem
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (i : alpha) (hi : i ∈ fiber) :
    U i ∈ retainedPairTubeFamily fiber T U := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- First endpoint curve of one retained rectangle. -/
def retainedPairFirstCurve
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (i : {i // i ∈ fiber}) :
    FirstGenerationCurve (retainedPairTubeFamily fiber T U) :=
  ⟨T i.1, retainedPair_first_mem fiber T U i.1 i.2⟩

/-- Second endpoint curve of one retained rectangle. -/
def retainedPairSecondCurve
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (i : {i // i ∈ fiber}) :
    FirstGenerationCurve (retainedPairTubeFamily fiber T U) :=
  ⟨U i.1, retainedPair_second_mem fiber T U i.1 i.2⟩

/-- The literal unordered endpoint pair attached to a retained rectangle. -/
def retainedFirstGenerationCurvePair
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (i : {i // i ∈ fiber}) :
    FirstGenerationCurvePair (retainedPairTubeFamily fiber T U) := by
  refine ⟨s(retainedPairFirstCurve fiber T U i,
    retainedPairSecondCurve fiber T U i), ?_⟩
  rw [Sym2.mk_isDiag_iff]
  intro heq
  exact hpairNe i.1 i.2 (congrArg Subtype.val heq)

/-- Distinct retained rectangles have distinct unordered actual-tube pairs. -/
def RetainedUnorderedPairInjective
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius) : Prop :=
  Function.Injective (fun i : {i // i ∈ fiber} =>
    s(retainedPairFirstCurve fiber T U i,
      retainedPairSecondCurve fiber T U i))

/-- Package the necessary distinct-pair bookkeeping as an embedding.  The
input is precisely injectivity of the unordered tube-pair label on retained
rectangle indices, rather than an already reindexed endpoint family. -/
def retainedFirstGenerationCurvePairEmbedding
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (hpairInjective : RetainedUnorderedPairInjective fiber T U) :
    {i // i ∈ fiber} ↪
      FirstGenerationCurvePair (retainedPairTubeFamily fiber T U) where
  toFun := retainedFirstGenerationCurvePair fiber T U hpairNe
  inj' := by
    intro i j hij
    exact hpairInjective (congrArg Subtype.val hij)

/-- Endpoint item set obtained by mapping every retained rectangle through
the explicit unordered-pair embedding. -/
def retainedFirstGenerationCurvePairItems
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (hpairInjective : RetainedUnorderedPairInjective fiber T U) :
    Finset (FirstGenerationCurvePair (retainedPairTubeFamily fiber T U)) :=
  fiber.attach.map
    (retainedFirstGenerationCurvePairEmbedding
      fiber T U hpairNe hpairInjective)

theorem retainedFirstGenerationCurvePairItems_card
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (hpairInjective : RetainedUnorderedPairInjective fiber T U) :
    (retainedFirstGenerationCurvePairItems
      fiber T U hpairNe hpairInjective).card = fiber.card := by
  simp only [retainedFirstGenerationCurvePairItems, Finset.card_map,
    Finset.card_attach]

/-- The retained-index subtype is explicitly equivalent to the endpoint item
subtype; this is the lossless reindexing used to transport rectangles and
pair-local certificates. -/
noncomputable def retainedIndexEquivEndpointItems
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (hpairInjective : RetainedUnorderedPairInjective fiber T U) :
    {i // i ∈ fiber} ≃
      {p // p ∈ retainedFirstGenerationCurvePairItems
        fiber T U hpairNe hpairInjective} := by
  let embedding := retainedFirstGenerationCurvePairEmbedding
    fiber T U hpairNe hpairInjective
  let items := retainedFirstGenerationCurvePairItems
    fiber T U hpairNe hpairInjective
  let forward : {i // i ∈ fiber} -> {p // p ∈ items} := fun i =>
    ⟨embedding i, by
      change embedding i ∈ fiber.attach.map embedding
      exact Finset.mem_map.mpr ⟨i, Finset.mem_attach fiber i, rfl⟩⟩
  apply Equiv.ofBijective forward
  constructor
  · intro i j hij
    exact embedding.injective (congrArg Subtype.val hij)
  · intro p
    have hp : p.1 ∈ items := p.2
    change p.1 ∈ fiber.attach.map embedding at hp
    rw [Finset.mem_map] at hp
    obtain ⟨i, _hi, hip⟩ := hp
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hip

/-- Complete endpoint-side data over the reindexed item subtype.  No default
values outside the item set and no fake pair-local certificate are introduced. -/
structure RetainedPairLocalEndpointItems
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f : Real -> Real) (A B delta t lambda0 : Real) where
  items : Finset (FirstGenerationCurvePair
    (retainedPairTubeFamily fiber T U))
  indexEquiv : {i // i ∈ fiber} ≃ {p // p ∈ items}
  firstTube : {p // p ∈ items} -> Tube radius
  secondTube : {p // p ∈ items} -> Tube radius
  rectangles : {p // p ∈ items} -> C2GraphRectangle
  first_mem : forall p, firstTube p ∈ retainedPairTubeFamily fiber T U
  second_mem : forall p, secondTube p ∈ retainedPairTubeFamily fiber T U
  pair_eq : forall p : {p // p ∈ items}, p.1.1 =
    s(⟨firstTube p, first_mem p⟩, ⟨secondTube p, second_mem p⟩)
  data : forall p : {p // p ∈ items}, PairLocalActualLensRectangleData
    (firstTube p) (secondTube p) f (rectangles p)
      A B delta t lambda0
  items_card : items.card = fiber.card

/-- Construct the complete retained-rectangle endpoint package without any
cardinality loss. -/
theorem exists_retainedPairLocalEndpointItems
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f : Real -> Real) (A B delta t lambda0 : Real)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (hpairInjective : RetainedUnorderedPairInjective fiber T U)
    (D : forall i, i ∈ fiber -> PairLocalActualLensRectangleData
      (T i) (U i) f (sourceRectangles i) A B delta t lambda0) :
    Nonempty (RetainedPairLocalEndpointItems
      fiber T U sourceRectangles f A B delta t lambda0) := by
  let items := retainedFirstGenerationCurvePairItems
    fiber T U hpairNe hpairInjective
  let E := retainedIndexEquivEndpointItems
    fiber T U hpairNe hpairInjective
  let sourceIndex : {p // p ∈ items} -> {i // i ∈ fiber} := E.symm
  let firstTube : {p // p ∈ items} -> Tube radius :=
    fun p => T (sourceIndex p).1
  let secondTube : {p // p ∈ items} -> Tube radius :=
    fun p => U (sourceIndex p).1
  let rectangles : {p // p ∈ items} -> C2GraphRectangle :=
    fun p => sourceRectangles (sourceIndex p).1
  have hfirstMem : forall p, firstTube p ∈
      retainedPairTubeFamily fiber T U := by
    intro p
    exact retainedPair_first_mem fiber T U
      (sourceIndex p).1 (sourceIndex p).2
  have hsecondMem : forall p, secondTube p ∈
      retainedPairTubeFamily fiber T U := by
    intro p
    exact retainedPair_second_mem fiber T U
      (sourceIndex p).1 (sourceIndex p).2
  have hpairEq : forall p : {p // p ∈ items}, p.1.1 =
      s(⟨firstTube p, hfirstMem p⟩, ⟨secondTube p, hsecondMem p⟩) := by
    intro p
    let i := sourceIndex p
    have hE : E i = p := E.apply_symm_apply p
    have hvalue : (E i).1 = p.1 := congrArg Subtype.val hE
    rw [← hvalue]
    rfl
  have hdata : forall p : {p // p ∈ items}, PairLocalActualLensRectangleData
      (firstTube p) (secondTube p) f (rectangles p)
        A B delta t lambda0 := by
    intro p
    exact D (sourceIndex p).1 (sourceIndex p).2
  exact ⟨{
    items := items
    indexEquiv := E
    firstTube := firstTube
    secondTube := secondTube
    rectangles := rectangles
    first_mem := hfirstMem
    second_mem := hsecondMem
    pair_eq := hpairEq
    data := hdata
    items_card := retainedFirstGenerationCurvePairItems_card
      fiber T U hpairNe hpairInjective
  }⟩

/-! ## Total endpoint interface -/

/-- A canonical ordered representative of the first member of an unordered
first-generation pair.  Its orientation is irrelevant outside retained
items. -/
noncomputable def firstGenerationCurvePairOutFirst
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (p : FirstGenerationCurvePair curves) :
    FirstGenerationCurve curves :=
  (Quot.out p.1).1

/-- The second member of the same canonical ordered representative. -/
noncomputable def firstGenerationCurvePairOutSecond
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (p : FirstGenerationCurvePair curves) :
    FirstGenerationCurve curves :=
  (Quot.out p.1).2

theorem firstGenerationCurvePair_eq_out
    {curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (p : FirstGenerationCurvePair curves) :
    p.1 = s(firstGenerationCurvePairOutFirst p,
      firstGenerationCurvePairOutSecond p) := by
  simpa only [firstGenerationCurvePairOutFirst,
    firstGenerationCurvePairOutSecond] using (Quot.out_eq p.1).symm

/-- The exact total function shape expected by the existing pair-local
Marcus--Tardos endpoint.  Outside retained items the unordered pair itself
supplies harmless canonical first/second curves; pair-local data are required
only on membership in the retained item set. -/
structure RetainedPairLocalEndpointInterface
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f : Real -> Real) (A B delta t lambda0 : Real) where
  items : Finset (FirstGenerationCurvePair
    (retainedPairTubeFamily fiber T U))
  firstTube : FirstGenerationCurvePair
    (retainedPairTubeFamily fiber T U) -> Tube radius
  secondTube : FirstGenerationCurvePair
    (retainedPairTubeFamily fiber T U) -> Tube radius
  rectangles : FirstGenerationCurvePair
    (retainedPairTubeFamily fiber T U) -> C2GraphRectangle
  first_mem : forall p, firstTube p ∈ retainedPairTubeFamily fiber T U
  second_mem : forall p, secondTube p ∈ retainedPairTubeFamily fiber T U
  pair_eq : forall p : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U), p.1 =
    s(⟨firstTube p, first_mem p⟩, ⟨secondTube p, second_mem p⟩)
  data : forall p, p ∈ items -> PairLocalActualLensRectangleData
    (firstTube p) (secondTube p) f (rectangles p)
      A B delta t lambda0
  items_card : items.card = fiber.card

/-- Extend the lossless retained-item subtype package to the total function
interface consumed by the endpoint.  The only reason for nonempty 'fiber' is
to choose an irrelevant default rectangle outside retained items. -/
theorem exists_total_retainedPairLocalEndpointInterface
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f : Real -> Real) (A B delta t lambda0 : Real)
    (hfiber : fiber.Nonempty)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (hpairInjective : RetainedUnorderedPairInjective fiber T U)
    (D : forall i, i ∈ fiber -> PairLocalActualLensRectangleData
      (T i) (U i) f (sourceRectangles i) A B delta t lambda0) :
    Nonempty (RetainedPairLocalEndpointInterface
      fiber T U sourceRectangles f A B delta t lambda0) := by
  obtain ⟨S⟩ := exists_retainedPairLocalEndpointItems
    fiber T U sourceRectangles f A B delta t lambda0
      hpairNe hpairInjective D
  obtain ⟨i0, _hi0⟩ := hfiber
  let firstTube : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U) -> Tube radius := fun p =>
    if hp : p ∈ S.items then S.firstTube ⟨p, hp⟩
    else (firstGenerationCurvePairOutFirst p).1
  let secondTube : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U) -> Tube radius := fun p =>
    if hp : p ∈ S.items then S.secondTube ⟨p, hp⟩
    else (firstGenerationCurvePairOutSecond p).1
  let rectangles : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U) -> C2GraphRectangle := fun p =>
    if hp : p ∈ S.items then S.rectangles ⟨p, hp⟩
    else sourceRectangles i0
  have hfirstMem : forall p, firstTube p ∈
      retainedPairTubeFamily fiber T U := by
    intro p
    by_cases hp : p ∈ S.items
    · simpa only [firstTube, dif_pos hp] using S.first_mem ⟨p, hp⟩
    · simpa only [firstTube, dif_neg hp] using
        (firstGenerationCurvePairOutFirst p).2
  have hsecondMem : forall p, secondTube p ∈
      retainedPairTubeFamily fiber T U := by
    intro p
    by_cases hp : p ∈ S.items
    · simpa only [secondTube, dif_pos hp] using S.second_mem ⟨p, hp⟩
    · simpa only [secondTube, dif_neg hp] using
        (firstGenerationCurvePairOutSecond p).2
  have hpairEq : forall p : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U), p.1 =
      s(⟨firstTube p, hfirstMem p⟩, ⟨secondTube p, hsecondMem p⟩) := by
    intro p
    by_cases hp : p ∈ S.items
    · simpa only [firstTube, secondTube, dif_pos hp] using
        S.pair_eq ⟨p, hp⟩
    · simpa only [firstTube, secondTube, dif_neg hp] using
        firstGenerationCurvePair_eq_out p
  have hdata : forall p, p ∈ S.items ->
      PairLocalActualLensRectangleData
        (firstTube p) (secondTube p) f (rectangles p)
          A B delta t lambda0 := by
    intro p hp
    simpa only [firstTube, secondTube, rectangles, dif_pos hp] using
      S.data ⟨p, hp⟩
  exact ⟨{
    items := S.items
    firstTube := firstTube
    secondTube := secondTube
    rectangles := rectangles
    first_mem := hfirstMem
    second_mem := hsecondMem
    pair_eq := hpairEq
    data := hdata
    items_card := S.items_card
  }⟩

#print axioms criticalHeightDifferenceSet_self_finite
#print axioms pairGeneralPositionBadParameters_finite
#print axioms familyGeneralPositionBadParameters_finite
#print axioms generalPosition_of_not_mem_familyBad
#print axioms exists_small_positive_generalPositionParameter
#print axioms actualTubeGraph_individuallyTracePerturbedTube
#print axioms actualTubeGraphFirst_individuallyTracePerturbedTube
#print axioms exists_small_positive_actualTubeGeneralPosition
#print axioms retainedFirstGenerationCurvePairItems_card
#print axioms retainedIndexEquivEndpointItems
#print axioms exists_retainedPairLocalEndpointItems
#print axioms firstGenerationCurvePair_eq_out
#print axioms exists_total_retainedPairLocalEndpointInterface

end

end FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
