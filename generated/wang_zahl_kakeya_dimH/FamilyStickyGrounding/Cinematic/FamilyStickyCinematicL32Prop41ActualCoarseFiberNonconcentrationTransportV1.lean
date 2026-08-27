import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalMaximizerHighPayloadAdapterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41ActualCoarseFiberNonconcentrationTransportV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerHighPayloadAdapterV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

noncomputable section

universe u v w

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Restricting canonical norm non-concentration to the actual coarse fibre

For a literal coarse rectangle `R`, the paper's family `F(R)` is
`D.coarseTubeFiber keep R`.  The canonical maximizer controls balls in its
actual local critical family.  Therefore the precise missing geometric link
is the theorem-level inclusion

`D.coarseTubeFiber keep R ⊆ N.family`.

It is deliberately a hypothesis rather than a field of either data record:
the present repository does not yet prove that every retained incidence over
`R` lies in the one local critical family selected at the high-payload point.
Once that inclusion is supplied, the restriction estimates below are genuine
cardinality consequences, not stored non-concentration callbacks.

The index-level statement needs one further logically necessary premise:
injectivity of the actual tube map on the coarse index fibre.  A convenient
corollary derives it from positive radius and essential distinctness on the
actual projected ambient family.
-/

/-- The part of the literal tube family `F(R)` in one closed metric ball. -/
noncomputable def _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.coarseTubeMetricBall
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (distance : Tube radius -> Tube radius -> Real)
    (ballRadius : Real) (center : Tube radius) : Finset (Tube radius) := by
  classical
  exact (D.coarseTubeFiber keep R).filter fun T =>
    distance T center <= ballRadius

@[simp]
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.mem_coarseTubeMetricBall_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {R : C2GraphRectangle}
    {distance : Tube radius -> Tube radius -> Real}
    {ballRadius : Real} {center T : Tube radius} :
    T ∈ D.coarseTubeMetricBall keep R distance ballRadius center <->
      T ∈ D.coarseTubeFiber keep R ∧ distance T center <= ballRadius := by
  classical
  simp [CoarseRectangleIncidenceData.coarseTubeMetricBall]

/-- Index-valued version of the same closed ball restriction. -/
def _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.coarseCurveMetricBall
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (distance : Tube radius -> Tube radius -> Real)
    (ballRadius : Real) (center : Tube radius) : Finset iota :=
  (D.coarseCurveIndexFiber keep R).filter fun i =>
    distance (D.fine.tubes i) center <= ballRadius

@[simp]
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.mem_coarseCurveMetricBall_iff
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {R : C2GraphRectangle}
    {distance : Tube radius -> Tube radius -> Real}
    {ballRadius : Real} {center : Tube radius} {i : iota} :
    i ∈ D.coarseCurveMetricBall keep R distance ballRadius center <->
      i ∈ D.coarseCurveIndexFiber keep R ∧
        distance (D.fine.tubes i) center <= ballRadius := by
  simp [CoarseRectangleIncidenceData.coarseCurveMetricBall]

/-- Every actual coarse index comes from the literal projected ambient
family, because membership in `F(R)` has a genuine good-incidence witness. -/
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.coarseCurveIndexFiber_subset_ambient
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle) :
    D.coarseCurveIndexFiber keep R ⊆ D.shading.ambient := by
  intro i hi
  obtain ⟨r, hgood, _hkeep, _hcoarse⟩ :=
    (D.mem_coarseCurveIndexFiber_iff keep).mp hi
  exact hgood.1

/-- Filtering indices and then taking their actual tubes gives exactly the
tube-valued ball restriction of `F(R)`.  This identity does not need
injectivity. -/
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.image_coarseCurveMetricBall_eq
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (distance : Tube radius -> Tube radius -> Real)
    (ballRadius : Real) (center : Tube radius) :
    (D.coarseCurveMetricBall keep R distance ballRadius center).image
        D.fine.tubes =
      D.coarseTubeMetricBall keep R distance ballRadius center := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hT
    have hiData := (D.mem_coarseCurveMetricBall_iff keep).mp hi
    exact (D.mem_coarseTubeMetricBall_iff keep).mpr
      ⟨(D.mem_coarseTubeFiber_iff (keep := keep)).mpr ⟨i, hiData.1, rfl⟩, hiData.2⟩
  · intro hT
    have hTData := (D.mem_coarseTubeMetricBall_iff keep).mp hT
    obtain ⟨i, hi, hTi⟩ :=
      (D.mem_coarseTubeFiber_iff (keep := keep)).mp hTData.1
    refine Finset.mem_image.mpr ⟨i, ?_, hTi⟩
    exact (D.mem_coarseCurveMetricBall_iff keep).mpr
      ⟨hi, hTi.symm ▸ hTData.2⟩

/-- Without deduplication information, the tube-valued `F(R)` ball can only
lose cardinality relative to its index-valued version. -/
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.coarseTubeMetricBall_card_le_curve
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (distance : Tube radius -> Tube radius -> Real)
    (ballRadius : Real) (center : Tube radius) :
    (D.coarseTubeMetricBall keep R distance ballRadius center).card <=
      (D.coarseCurveMetricBall keep R distance ballRadius center).card := by
  rw [← D.image_coarseCurveMetricBall_eq keep R distance ballRadius center]
  exact Finset.card_image_le

/-- If the actual tube map is injective on the coarse index fibre, the
index- and tube-valued ball restrictions have exactly the same cardinality. -/
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.coarseCurveMetricBall_card_eq_tube
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (distance : Tube radius -> Tube radius -> Real)
    (ballRadius : Real) (center : Tube radius)
    (hinjective : Set.InjOn D.fine.tubes
      (D.coarseCurveIndexFiber keep R : Set iota)) :
    (D.coarseCurveMetricBall keep R distance ballRadius center).card =
      (D.coarseTubeMetricBall keep R distance ballRadius center).card := by
  classical
  rw [← D.image_coarseCurveMetricBall_eq keep R distance ballRadius center]
  symm
  apply Finset.card_image_iff.mpr
  intro i hi j hj hij
  exact hinjective
    ((D.mem_coarseCurveMetricBall_iff keep).mp hi).1
    ((D.mem_coarseCurveMetricBall_iff keep).mp hj).1 hij

/-- The sole geometric inclusion needed for restriction transports an
`F(R)` ball into the corresponding canonical-family ball. -/
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.coarseTubeMetricBall_subset
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (family : Finset (Tube radius))
    (distance : Tube radius -> Tube radius -> Real)
    (ballRadius : Real) (center : Tube radius)
    (hfiber : D.coarseTubeFiber keep R ⊆ family) :
    D.coarseTubeMetricBall keep R distance ballRadius center ⊆
      finiteFamilyMetricBall family distance ballRadius center := by
  intro T hT
  have hTData := (D.mem_coarseTubeMetricBall_iff keep).mp hT
  exact Finset.mem_filter.mpr ⟨hfiber hTData.1, hTData.2⟩

/-- Canonical norm non-concentration restricted to the actual tube-valued
paper family `F(R)`. -/
theorem coarseTubeMetricBall_card_le_ratio_rpow
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData (Tube radius))
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hfiber : D.coarseTubeFiber keep R ⊆ N.family)
    {ballRadius : Real} (hradiusLower : N.delta <= ballRadius)
    (hradiusUpper : ballRadius <= N.ceiling)
    (center : Tube radius) (hcenter : center ∈ N.family) :
    ((D.coarseTubeMetricBall keep R N.distance ballRadius center).card : Real) <=
      (ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real) := by
  have hsubset := D.coarseTubeMetricBall_subset keep R N.family N.distance
    ballRadius center hfiber
  have hcardNat := Finset.card_le_card hsubset
  have hcardReal :
      ((D.coarseTubeMetricBall keep R N.distance ballRadius center).card : Real) <=
        (finiteBallCount N.family N.distance ballRadius center : Real) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans
    (N.card_le_ratio_rpow hradiusLower hradiusUpper center hcenter)

/-- Lossless index-level version under the minimal injectivity premise. -/
theorem coarseCurveMetricBall_card_le_ratio_rpow
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData (Tube radius))
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hfiber : D.coarseTubeFiber keep R ⊆ N.family)
    (hinjective : Set.InjOn D.fine.tubes
      (D.coarseCurveIndexFiber keep R : Set iota))
    {ballRadius : Real} (hradiusLower : N.delta <= ballRadius)
    (hradiusUpper : ballRadius <= N.ceiling)
    (center : Tube radius) (hcenter : center ∈ N.family) :
    ((D.coarseCurveMetricBall keep R N.distance ballRadius center).card : Real) <=
      (ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real) := by
  rw [D.coarseCurveMetricBall_card_eq_tube keep R N.distance ballRadius
    center hinjective]
  exact coarseTubeMetricBall_card_le_ratio_rpow N D keep R hfiber
    hradiusLower hradiusUpper center hcenter

/-- A centre already in the actual `F(R)` is retained by its restricted ball
whenever its self-distance is at most the ball radius. -/
theorem _root_.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1.CoarseRectangleIncidenceData.center_mem_coarseTubeMetricBall
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (distance : Tube radius -> Tube radius -> Real)
    (ballRadius : Real) (center : Tube radius)
    (hcenterFiber : center ∈ D.coarseTubeFiber keep R)
    (hself : distance center center <= ballRadius) :
    center ∈ D.coarseTubeMetricBall keep R distance ballRadius center :=
  (D.mem_coarseTubeMetricBall_iff keep).mpr ⟨hcenterFiber, hself⟩

section ActualHighPayload

variable {point : Type u} [MeasurableSpace point]
variable {radius : NNReal} {iota : Type v} [DecidableEq iota]
variable {fineLabel : Type w} [DecidableEq fineLabel]
variable {muMeasure : Measure point} {base : Set point}
variable {hbase : MeasurableSet base}
variable {fine : UniformTubeFamily radius iota}
variable {physical : FiniteProjectedShading point iota}
variable {f f1 f2 : Real -> Real} {outerA outerB : Real}
variable {hOuter : outerA <= outerB}
variable {hf : forall z, HasDerivAt f (f1 z) z}
variable {hf1 : forall z, HasDerivAt f1 (f2 z) z}
variable {globalScale : Real} {globalCenter : Tube radius}
variable {tangencyExponent normExponent : Real} {logCount : Nat}

/-- Direct high-branch endpoint: no new high-payload premise is requested.
Only the still-missing coarse-to-local-critical-family inclusion is supplied. -/
theorem _root_.FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1.ActualHighPayloadWithNormNonconcentration.coarseTubeMetricBall_card_le
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hfiber : D.coarseTubeFiber keep R ⊆ P.normData.family)
    {ballRadius : Real} (hradiusLower : (radius : Real) <= ballRadius)
    (hradiusUpper : ballRadius <= 16)
    (center : Tube radius) (hcenter : center ∈ P.normData.family) :
    ((D.coarseTubeMetricBall keep R projectedTubePairCoefficientDistance
        ballRadius center).card : Real) <=
      (ballRadius / P.normData.criticalScale) ^ normExponent *
        ((P.normData.criticalBall.card : Nat) : Real) := by
  exact coarseTubeMetricBall_card_le_ratio_rpow P.normData D keep R hfiber
    hradiusLower hradiusUpper center hcenter

/-- The same actual high-branch bound pulled losslessly back to curve indices.
Ambient essential distinctness is the geometric source of injectivity. -/
theorem _root_.FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1.ActualHighPayloadWithNormNonconcentration.coarseCurveMetricBall_card_le
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hfiber : D.coarseTubeFiber keep R ⊆ P.normData.family)
    (hpair : Set.Pairwise (D.shading.ambient : Set iota) fun i j =>
      EssentiallyDistinct (D.fine.tubes i) (D.fine.tubes j))
    {ballRadius : Real} (hradiusLower : (radius : Real) <= ballRadius)
    (hradiusUpper : ballRadius <= 16)
    (center : Tube radius) (hcenter : center ∈ P.normData.family) :
    ((D.coarseCurveMetricBall keep R projectedTubePairCoefficientDistance
        ballRadius center).card : Real) <=
      (ballRadius / P.normData.criticalScale) ^ normExponent *
        ((P.normData.criticalBall.card : Nat) : Real) := by
  have hpairFiber : Set.Pairwise
      (D.coarseCurveIndexFiber keep R : Set iota) fun i j =>
        EssentiallyDistinct (D.fine.tubes i) (D.fine.tubes j) := by
    intro i hi j hj hij
    exact hpair (D.coarseCurveIndexFiber_subset_ambient keep R hi)
      (D.coarseCurveIndexFiber_subset_ambient keep R hj) hij
  have hinjective := tubes_injectiveOn_active_of_essentiallyDistinct D.fine
    (D.coarseCurveIndexFiber keep R) P.radius_pos hpairFiber
  exact coarseCurveMetricBall_card_le_ratio_rpow P.normData D keep R hfiber
    hinjective hradiusLower hradiusUpper center hcenter

/-- Two selected centres in one and the same actual `F(R)` give nonempty
(hence `1`-rich) restricted balls, while the canonical maximizer supplies
both upper bounds.  This is the strongest richness conclusion requiring no
separate paper lower-bound theorem. -/
theorem _root_.FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1.ActualHighPayloadWithNormNonconcentration.sameCoarseFiber_twoBall_one_rich
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hfiber : D.coarseTubeFiber keep R ⊆ P.normData.family)
    {ballRadius : Real} (hradiusLower : (radius : Real) <= ballRadius)
    (hradiusUpper : ballRadius <= 16)
    (left right : Tube radius)
    (hleft : left ∈ D.coarseTubeFiber keep R)
    (hright : right ∈ D.coarseTubeFiber keep R) :
    1 <= (D.coarseTubeMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius left).card ∧
      ((D.coarseTubeMetricBall keep R
          projectedTubePairCoefficientDistance ballRadius left).card : Real) <=
        (ballRadius / P.normData.criticalScale) ^ normExponent *
          ((P.normData.criticalBall.card : Nat) : Real) ∧
      1 <= (D.coarseTubeMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius right).card ∧
      ((D.coarseTubeMetricBall keep R
          projectedTubePairCoefficientDistance ballRadius right).card : Real) <=
        (ballRadius / P.normData.criticalScale) ^ normExponent *
          ((P.normData.criticalBall.card : Nat) : Real) := by
  have hselfLeft : projectedTubePairCoefficientDistance left left <=
      ballRadius := by
    rw [projectedTubePairCoefficientDistance_self]
    exact (show (0 : Real) <= (radius : Real) from by positivity).trans
      hradiusLower
  have hselfRight : projectedTubePairCoefficientDistance right right <=
      ballRadius := by
    rw [projectedTubePairCoefficientDistance_self]
    exact (show (0 : Real) <= (radius : Real) from by positivity).trans
      hradiusLower
  have hleftMem := D.center_mem_coarseTubeMetricBall keep R
    projectedTubePairCoefficientDistance ballRadius left hleft hselfLeft
  have hrightMem := D.center_mem_coarseTubeMetricBall keep R
    projectedTubePairCoefficientDistance ballRadius right hright hselfRight
  have hleftUpper := P.coarseTubeMetricBall_card_le D keep R hfiber
    hradiusLower hradiusUpper left (hfiber hleft)
  have hrightUpper := P.coarseTubeMetricBall_card_le D keep R hfiber
    hradiusLower hradiusUpper right (hfiber hright)
  exact ⟨Finset.one_le_card.mpr ⟨left, hleftMem⟩, hleftUpper,
    Finset.one_le_card.mpr ⟨right, hrightMem⟩, hrightUpper⟩

/-- Paper-ready two-ball interface.  The lower payload theorem is represented
by index-level richness hypotheses `hmu` and `hnu`.  Ambient essential
distinctness makes the actual tube map injective, so both lower bounds
transport without loss to the tube-valued restrictions of the same literal
`F(R)`; the canonical maximizer then derives both upper bounds. -/
theorem _root_.FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1.ActualHighPayloadWithNormNonconcentration.sameCoarseFiber_twoBall_mu_nu
    (P : ActualHighPayloadWithNormNonconcentration muMeasure base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (R : C2GraphRectangle)
    (hfiber : D.coarseTubeFiber keep R ⊆ P.normData.family)
    (hpair : Set.Pairwise (D.shading.ambient : Set iota) fun i j =>
      EssentiallyDistinct (D.fine.tubes i) (D.fine.tubes j))
    {ballRadius : Real} (hradiusLower : (radius : Real) <= ballRadius)
    (hradiusUpper : ballRadius <= 16)
    (left right : Tube radius)
    (hleft : left ∈ D.coarseTubeFiber keep R)
    (hright : right ∈ D.coarseTubeFiber keep R)
    (mu nu : Nat)
    (hmu : mu <= (D.coarseCurveMetricBall keep R
      projectedTubePairCoefficientDistance ballRadius left).card)
    (hnu : nu <= (D.coarseCurveMetricBall keep R
      projectedTubePairCoefficientDistance ballRadius right).card) :
    mu <= (D.coarseTubeMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius left).card ∧
      ((D.coarseTubeMetricBall keep R
          projectedTubePairCoefficientDistance ballRadius left).card : Real) <=
        (ballRadius / P.normData.criticalScale) ^ normExponent *
          ((P.normData.criticalBall.card : Nat) : Real) ∧
      nu <= (D.coarseTubeMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius right).card ∧
      ((D.coarseTubeMetricBall keep R
          projectedTubePairCoefficientDistance ballRadius right).card : Real) <=
        (ballRadius / P.normData.criticalScale) ^ normExponent *
          ((P.normData.criticalBall.card : Nat) : Real) := by
  have hpairFiber : Set.Pairwise
      (D.coarseCurveIndexFiber keep R : Set iota) fun i j =>
        EssentiallyDistinct (D.fine.tubes i) (D.fine.tubes j) := by
    intro i hi j hj hij
    exact hpair (D.coarseCurveIndexFiber_subset_ambient keep R hi)
      (D.coarseCurveIndexFiber_subset_ambient keep R hj) hij
  have hinjective := tubes_injectiveOn_active_of_essentiallyDistinct D.fine
    (D.coarseCurveIndexFiber keep R) P.radius_pos hpairFiber
  have hleftCard := D.coarseCurveMetricBall_card_eq_tube keep R
    projectedTubePairCoefficientDistance ballRadius left hinjective
  have hrightCard := D.coarseCurveMetricBall_card_eq_tube keep R
    projectedTubePairCoefficientDistance ballRadius right hinjective
  have hmuTube : mu <= (D.coarseTubeMetricBall keep R
      projectedTubePairCoefficientDistance ballRadius left).card :=
    hmu.trans_eq hleftCard
  have hnuTube : nu <= (D.coarseTubeMetricBall keep R
      projectedTubePairCoefficientDistance ballRadius right).card :=
    hnu.trans_eq hrightCard
  have hbounds := P.sameCoarseFiber_twoBall_one_rich D keep R hfiber
    hradiusLower hradiusUpper left right hleft hright
  exact ⟨hmuTube, hbounds.2.1, hnuTube, hbounds.2.2.2⟩

end ActualHighPayload

#print axioms CoarseRectangleIncidenceData.coarseCurveIndexFiber_subset_ambient
#print axioms CoarseRectangleIncidenceData.image_coarseCurveMetricBall_eq
#print axioms CoarseRectangleIncidenceData.coarseCurveMetricBall_card_eq_tube
#print axioms CoarseRectangleIncidenceData.coarseTubeMetricBall_subset
#print axioms coarseTubeMetricBall_card_le_ratio_rpow
#print axioms coarseCurveMetricBall_card_le_ratio_rpow
#print axioms ActualHighPayloadWithNormNonconcentration.coarseTubeMetricBall_card_le
#print axioms ActualHighPayloadWithNormNonconcentration.coarseCurveMetricBall_card_le
#print axioms ActualHighPayloadWithNormNonconcentration.sameCoarseFiber_twoBall_one_rich
#print axioms ActualHighPayloadWithNormNonconcentration.sameCoarseFiber_twoBall_mu_nu

end

end FamilyStickyCinematicL32Prop41ActualCoarseFiberNonconcentrationTransportV1
