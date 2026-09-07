import Family8Grounding.Family8PlankLongTubeOptimalKatzTaoFreshV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2
import Family8Grounding.Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1
import Mathlib.Tactic

/-!
# A non-circular Frostman-parameter connector for normalized plank rows

This file records the part of the paper's plank argument that is already
available without a convex-plank multiplicity hypothesis.  A shaded
`a x b x 1` plank family is replaced by its genuine radius-`b` long-tube
cover, translated to the origin, dilated by `1 / 8`, and freshly refined to
an admissible actual tube datum.  `FrostmanAtParameters` can then be applied
directly to that datum.

The conclusion deliberately retains

`freshLoss * frostmanMultiplicityRHS (b / 8) refinedVolume ...`.

In particular, it is not yet the Family 7 convex-plank bound.  Converting the
displayed quantity to `convexPlankFrostmanFactor`, with its
`CF ^ (1 - beta / 2)` dependence, is precisely the still-missing
copied-cardinality/refined-volume interpolation from the generalized
Frostman argument (paper Lemmas 3.8--3.9).  No `BoundAt`, fixed-geometry, or
stable convex-plank multiplicity hypothesis is consumed here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankLongTubeFrostmanAtParametersProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeFrostmanTransferV3
open Family8PlankLongTubeCenteredFreshV4
open Family8PlankLongTubeOptimalKatzTaoFreshV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1

noncomputable section

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The actual tube datum obtained from a plank family before the final
eighth-normalization and fresh restriction.  Its index has one literal copy;
the `Unit` is kept to match the rigid-copy API. -/
abbrev plankLongTubeNormalizedSource
    (D : ShadedConvexPlankFamily iota a b) :
    ActualTubeDatum b (Unit × iota) :=
  centeredPlankLongTubeActualDatum D

/-- The genuine tube radius after the common unit-ball normalization. -/
def plankLongTubeNormalizedRadius (_D : ShadedConvexPlankFamily iota a b) :
    NNReal :=
  b / 8

/-- The deterministic conflict threshold used by the optimal fresh selector. -/
def plankLongTubeFreshThreshold
    (D : ShadedConvexPlankFamily iota a b) : Nat :=
  Nat.ceil
    ((480000 * (128 * plankLongTubeOptimalKatzTaoConstant D) : ENNReal).toReal)

/-- The exact mass/cardinality loss of the fresh greedy restriction. -/
def plankLongTubeFreshLoss
    (D : ShadedConvexPlankFamily iota a b) : ENNReal :=
  ((plankLongTubeFreshThreshold D + 1 : Nat) : ENNReal)

/-- The selected, genuinely admissible actual tube datum to which the source
Frostman property is applied. -/
def plankLongTubeRefinedDatum
    (D : ShadedConvexPlankFamily iota a b)
    (selected : Finset (Unit × iota)) :
    ActualTubeDatum (plankLongTubeNormalizedRadius D) {p // p ∈ selected} :=
  restrictActualTubeDatum
    (eighthNormalizedDatum (plankLongTubeNormalizedSource D)) selected

/-- A nonempty plank family has positive long width. -/
theorem longWidth_pos_of_nonempty
    [Nonempty iota] (D : ShadedConvexPlankFamily iota a b) : 0 < b := by
  let i : iota := Classical.choice (inferInstance : Nonempty iota)
  exact (D.all_isPlank i).1.trans_le (D.all_isPlank i).2.1

/-- A nonempty actual plank family has positive indexed body volume. -/
theorem plankFamily_familyVolume_pos
    [Nonempty iota] (D : ShadedConvexPlankFamily iota a b) :
    0 < familyVolume D.family := by
  classical
  let i : iota := Classical.choice (inferInstance : Nonempty iota)
  have hi : 0 < volume (D.family i : Set Space) :=
    (D.all_isPlank i).volume_pos
  have hle : volume (D.family i : Set Space) ≤
      ∑ j : iota, volume (D.family j : Set Space) :=
    Finset.single_le_sum
      (f := fun j : iota ↦ volume (D.family j : Set Space))
      (fun _ _ ↦ bot_le) (Finset.mem_univ i)
  exact hi.trans_le hle

/-- The complete output retained from one direct use of
`FrostmanAtParameters`.  The structural fields expose the same fresh
selection that occurs in the final multiplicity inequality, so a later
volume/interpolation argument can use them without another choice. -/
def PlankLongTubeFrostmanAtParametersEndpoint
    (D : ShadedConvexPlankFamily iota a b)
    (epsilon beta : Real) : Prop :=
  ∃ selected : Finset (Unit × iota),
    selected.Nonempty ∧
    (restrictActualTubeDatum
      (eighthNormalizedDatum (centeredPlankLongTubeActualDatum D))
        selected).IsAdmissible ∧
    (Fintype.card (Unit × iota) : ENNReal) ≤
      plankLongTubeFreshLoss D * (selected.card : ENNReal) ∧
    (eighthNormalizedDatum
        (centeredPlankLongTubeActualDatum D)).shading.shadingMass ≤
      plankLongTubeFreshLoss D *
        (restrictActualTubeDatum
          (eighthNormalizedDatum (centeredPlankLongTubeActualDatum D))
            selected).shading.shadingMass ∧
    IsKatzTao (128 * plankLongTubeOptimalKatzTaoConstant D)
      (restrictActualTubeDatum
        (eighthNormalizedDatum (centeredPlankLongTubeActualDatum D))
          selected).family.bodyFamily ∧
    D.shading.averageMultiplicity ≤
      plankLongTubeFreshLoss D *
        frostmanMultiplicityRHS (plankLongTubeNormalizedRadius D)
          (restrictActualTubeDatum
            (eighthNormalizedDatum (centeredPlankLongTubeActualDatum D))
              selected).actualFamilyVolume
          epsilon beta

/-- Fixed-parameter, non-circular connector from a plank family to an actual
Frostman-property application.  Its only unresolved inputs are the terminal
scale comparison and the two scalar hypotheses needed to make the freshly
selected datum satisfy `FrostmanHypotheses` in the unit ball. -/
theorem exists_plankLongTube_refinement_frostmanAtParameters
    [Nonempty iota]
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ShadedConvexPlankFamily iota a b)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hdelta0 : plankLongTubeNormalizedRadius D ≤ delta0)
    (hdensityBudget :
      ((plankLongTubeNormalizedRadius D : NNReal) : ENNReal) ^ eta ≤
        (eighthNormalizedDatum
          (plankLongTubeNormalizedSource D)).shading.shadingDensity /
            plankLongTubeFreshLoss D)
    (hbaseBudget :
      plankLongTubeFreshLoss D *
          ((128 * plankLongTubeOptimalKatzTaoConstant D) *
            volume (unitBallBody : Set Space)) ≤
        ((plankLongTubeNormalizedRadius D : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card (Unit × iota) : ENNReal) *
            (((plankLongTubeNormalizedRadius D : NNReal) : ENNReal) ^ 2 / 2))) :
    PlankLongTubeFrostmanAtParametersEndpoint D epsilon beta := by
  let source := plankLongTubeNormalizedSource D
  let Copt := plankLongTubeOptimalKatzTaoConstant D
  let threshold := plankLongTubeFreshThreshold D
  let loss : ENNReal := ((threshold + 1 : Nat) : ENNReal)
  have hbPos : 0 < b := longWidth_pos_of_nonempty D
  have hfamily0 : familyVolume D.family ≠ 0 :=
    (plankFamily_familyVolume_pos D).ne'
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, _hsourceAverage⟩ :=
    exists_centeredPlankLongTube_fresh_admissible_optimal
      D hbPos hbHalf hfamily0
  have hloss0 : loss ≠ 0 := by
    dsimp only [loss]
    simp
  have hlossTop : loss ≠ ∞ := by
    dsimp only [loss]
    exact ENNReal.coe_ne_top
  have hsourceBound : source.shading.averageMultiplicity ≤
      loss * frostmanMultiplicityRHS (b / 8)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) selected).actualFamilyVolume
        epsilon beta := by
    exact source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS
      hF source selected loss (128 * Copt) hloss0 hlossTop hdelta0
        hadmissible hcard hmass hselectedKT hdensityBudget hbaseBudget
  have hplankSource : D.shading.averageMultiplicity ≤
      source.shading.averageMultiplicity := by
    exact source_averageMultiplicity_le_centeredPlankLongTubeActualDatum D
  refine ⟨selected, hselected, ?_, ?_, ?_, ?_, ?_⟩
  · exact hadmissible
  · simpa only [plankLongTubeFreshLoss, plankLongTubeFreshThreshold,
      threshold, loss] using hcard
  · simpa only [plankLongTubeFreshLoss, plankLongTubeFreshThreshold,
      threshold, loss] using hmass
  · exact hselectedKT
  · simpa only [plankLongTubeNormalizedRadius,
      plankLongTubeFreshLoss, plankLongTubeFreshThreshold, threshold, loss,
      source] using hplankSource.trans hsourceBound

/-- Property-level lift with the quantifiers in their correct order.  The
source property chooses `eta` and `delta0` uniformly; each later plank family
then needs exactly the displayed scale, density, and base budgets. -/
theorem exists_parameters_plankLongTube_refinement_frostman
    {beta epsilon : Real}
    (hF : FrostmanProperty beta) (hepsilon : 0 < epsilon) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
      ∀ {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
        {a b : NNReal} (D : ShadedConvexPlankFamily iota a b),
        b ≤ (2 : NNReal)⁻¹ →
        plankLongTubeNormalizedRadius D ≤ delta0 →
        ((plankLongTubeNormalizedRadius D : NNReal) : ENNReal) ^ eta ≤
            (eighthNormalizedDatum
              (plankLongTubeNormalizedSource D)).shading.shadingDensity /
                plankLongTubeFreshLoss D →
        plankLongTubeFreshLoss D *
              ((128 * plankLongTubeOptimalKatzTaoConstant D) *
                volume (unitBallBody : Set Space)) ≤
            ((plankLongTubeNormalizedRadius D : NNReal) : ENNReal) ^ (-eta) *
              ((Fintype.card (Unit × iota) : ENNReal) *
                (((plankLongTubeNormalizedRadius D : NNReal) : ENNReal) ^ 2 /
                  2)) →
        PlankLongTubeFrostmanAtParametersEndpoint D epsilon beta := by
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half, hAt⟩ :=
    hF.exists_parameters hepsilon
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_⟩
  intro iota _ _ _ a b D hbHalf hscale hdensity hbase
  exact exists_plankLongTube_refinement_frostmanAtParameters
    hAt D hbHalf hscale hdensity hbase

/-! ## The canonical actual tube datum on a fixed-theta normalized row -/

/-- The normalized affine row, converted definitionally to its genuine
centered radius-`longWidth` tube datum. -/
abbrev normalizedRowLongTubeSource
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    ActualTubeDatum (P.longWidth r)
      (Unit × {s // s ∈ R.rowOwners r}) :=
  plankLongTubeNormalizedSource (P.normalizedRowDatum r)

/-- The explicit certified member-volume comparison paid by the long-tube
cover of one affine-normalized row. -/
def normalizedRowLongTubeCopyLoss
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) : ENNReal :=
  plankLongTubeFrostmanCopyLoss
    (P.normalizedRowDatum r).comparisonConstant
    (P.shortWidth r) (P.longWidth r)

/-- The exact endpoint produced on one normalized row. -/
abbrev normalizedRowFrostmanEndpoint
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (epsilon beta : Real) (r : rowIndex) : Prop :=
  PlankLongTubeFrostmanAtParametersEndpoint
    (P.normalizedRowDatum r) epsilon beta

/-- The weakest all-row package for the already-constructed direct Frostman
connector.  It contains no geometric callback: long-tube construction,
centering, unit-ball support, and fresh essential distinctness are proved by
the imported construction.  The remaining fields are precisely the common
terminal scale and the two scalar Frostman-hypothesis budgets. -/
structure FixedThetaAllSlabNormalizedRowsFrostmanBudgets
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (eta : Real) (delta0 : NNReal) : Prop where
  longWidth_le_half : ∀ r, P.longWidth r ≤ (2 : NNReal)⁻¹
  terminalScale : ∀ r,
    plankLongTubeNormalizedRadius (P.normalizedRowDatum r) ≤ delta0
  density : ∀ r,
    ((plankLongTubeNormalizedRadius
      (P.normalizedRowDatum r) : NNReal) : ENNReal) ^ eta ≤
      (eighthNormalizedDatum
        (normalizedRowLongTubeSource P r)).shading.shadingDensity /
          plankLongTubeFreshLoss (P.normalizedRowDatum r)
  unitBallBase : ∀ r,
    plankLongTubeFreshLoss (P.normalizedRowDatum r) *
          ((128 * plankLongTubeOptimalKatzTaoConstant
              (P.normalizedRowDatum r)) *
            volume (unitBallBody : Set Space)) ≤
      ((plankLongTubeNormalizedRadius
        (P.normalizedRowDatum r) : NNReal) : ENNReal) ^ (-eta) *
        ((Fintype.card
            (Unit × {s // s ∈ R.rowOwners r}) : ENNReal) *
          (((plankLongTubeNormalizedRadius
            (P.normalizedRowDatum r) : NNReal) : ENNReal) ^ 2 / 2))

/-- Apply the source Frostman property, at fixed chosen parameters, to every
literal affine-normalized row.  The `Unit`-universe restriction is forced by
the current definition of `FrostmanAtParameters`, whose quantified index type
is `Type` rather than `Type u`. -/
theorem normalizedRows_frostmanAtParameters
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (H : FixedThetaAllSlabNormalizedRowsFrostmanBudgets P eta delta0) :
    ∀ r, normalizedRowFrostmanEndpoint P epsilon beta r := by
  intro r
  have hrowNonempty : Nonempty {s // s ∈ R.rowOwners r} := by
    obtain ⟨s, hs⟩ := R.rowOwners_nonempty r
    exact ⟨⟨s, hs⟩⟩
  let _ : Nonempty {s // s ∈ R.rowOwners r} := hrowNonempty
  exact exists_plankLongTube_refinement_frostmanAtParameters
    hF (P.normalizedRowDatum r) (H.longWidth_le_half r)
      (H.terminalScale r) (H.density r) (H.unitBallBase r)

/-- Quantifier-correct all-row lift from `FrostmanProperty`.  The source
property is opened exactly once, before the later fixed-theta geometry is
chosen.  The same `eta` and `delta0` therefore govern every row. -/
theorem exists_parameters_normalizedRows_frostman
    {beta epsilon : Real}
    (hF : FrostmanProperty beta) (hepsilon : 0 < epsilon) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
      ∀ {iota : Type} [Fintype iota] [DecidableEq iota]
        {a b theta : NNReal}
        {D : ShadedConvexPlankFamily iota a b}
        {C : MutualThickeningClustering D theta}
        {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
        {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
        {slabComparisonConstant : NNReal}
        {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
        {normalize : rowIndex → Space ≃ᵃ[Real] Space}
        (P : FixedThetaAllSlabRowNormalizationGeometry R normalize),
        FixedThetaAllSlabNormalizedRowsFrostmanBudgets P eta delta0 →
          ∀ r, normalizedRowFrostmanEndpoint P epsilon beta r := by
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half, hAt⟩ :=
    hF.exists_parameters hepsilon
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_⟩
  intro iota _ _ a b theta D C q rowIndex _ _ slabComparisonConstant
    R normalize P H
  exact normalizedRows_frostmanAtParameters P hAt H

#print axioms longWidth_pos_of_nonempty
#print axioms plankFamily_familyVolume_pos
#print axioms exists_plankLongTube_refinement_frostmanAtParameters
#print axioms exists_parameters_plankLongTube_refinement_frostman
#print axioms normalizedRows_frostmanAtParameters
#print axioms exists_parameters_normalizedRows_frostman

end
end Family8PlankLongTubeFrostmanAtParametersProducerV1
