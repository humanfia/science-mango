import «ExactRadiusCellAdapter»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open BallwiseLocalVolumeUniformization
open CubeWeightUniformization
open CubeWeightMaster
open ExactRadiusCellAdapter

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace CubeWeightExactRadiusMaster

/-- Compactness alone makes the packing number finite and hence supplies an
actual finite maximal separated packing. -/
theorem exists_packingCertificate_of_isCompact
    {A : Set Space} (hcompact : IsCompact A)
    (r : ℝ≥0) (hr : 0 < r) :
    Nonempty (PackingCertificate A r) := by
  have htot : TotallyBounded A := hcompact.totallyBounded
  obtain ⟨N, _hNsub, hNfinite, hNcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded
      (ε := r) hr.ne' htot
  have hext_lt_top : Metric.externalCoveringNumber r A < ⊤ :=
    hNcover.externalCoveringNumber_le_encard.trans_lt hNfinite.encard_lt_top
  have hpack : Metric.packingNumber (2 * r) A ≠ ⊤ :=
    ((Metric.packingNumber_two_mul_le_externalCoveringNumber r A).trans_lt
      hext_lt_top).ne
  let S : Set Space := Metric.maximalSeparatedSet (2 * r) A
  have hSfinite : S.Finite := by
    rw [← Set.encard_lt_top_iff]
    rw [show S.encard = Metric.packingNumber (2 * r) A by
      simpa [S] using Metric.encard_maximalSeparatedSet hpack]
    exact hpack.lt_top
  refine ⟨{
    centers := hSfinite.toFinset
    centers_subset := ?_
    separated := ?_
    cover := ?_ }⟩
  · simpa [S] using (Metric.maximalSeparatedSet_subset :
      Metric.maximalSeparatedSet (2 * r) A ⊆ A)
  · simpa [S] using
      (Metric.isSeparated_maximalSeparatedSet :
        Metric.IsSeparated (2 * r)
          (Metric.maximalSeparatedSet (2 * r) A : Set Space))
  · simpa [S] using Metric.isCover_maximalSeparatedSet hpack

/-- The compact union of two finite convex families automatically supplies
the half-target-radius packing certificate; no shading compactness or external
container is needed. -/
theorem exists_finiteFamily_halfRadius_packingCertificate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ConvexFamily ι) (W : ConvexFamily κ)
    {rho : ℝ≥0} (hrho : 0 < rho) :
    Nonempty (PackingCertificate (familyUnion F ∪ familyUnion W)
      ((rho / 2) / 3)) := by
  apply exists_packingCertificate_of_isCompact
    ((familyUnion_isCompact F).union (familyUnion_isCompact W))
  positivity

/-- A single frame box containing the two finite carrier unions supplies the
packing certificate needed at half the target radius.  No compactness of either
shaded union is required. -/
theorem exists_halfRadius_packingCertificate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ConvexFamily ι) (W : ConvexFamily κ)
    (B : FrameBox)
    (hbox : familyUnion F ∪ familyUnion W ⊆ B.carrier)
    {rho : ℝ≥0} (hrho : 0 < rho) :
    Nonempty (PackingCertificate (familyUnion F ∪ familyUnion W)
      ((rho / 2) / 3)) := by
  exact exists_packingCertificate B hbox ((rho / 2) / 3) (by positivity)

/-- The weighted-cell master theorem, with the same selected fine/coarse
shadings and cell weight, upgraded to exact-radius local volume bounds at every
point of the final coarse shaded union. -/
theorem exists_common_weightedPackingLevel_exactRadius
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (fine : Shading F) (frozenCoarse : Shading W)
    {A : Set Space} (hA : MeasurableSet A) {rho : ℝ≥0}
    (C : PackingCertificate A ((rho / 2) / 3)) (hrho : 0 < rho)
    (hFineA : fine.shadedUnion ⊆ A)
    (K : ℕ) (hK : 0 < K)
    (hpoint : ∀ x, fine.pointMultiplicity x ≤ K)
    (hpositive : 0 < fine.shadingMass.toNNReal)
    (hcover : fine.shadedUnion ⊆ frozenCoarse.shadedUnion)
    (D : ℝ≥0∞) (hD : D ≤ fine.shadingMass) :
    ∃ n, n ≤ cubeExponent (a := Fin C.centers.card) K ∧
      let cell := packingCellFin C
      let hcell := measurableSet_packingCellFin hA C
      let mass := fun q ↦ cellMass fine cell hcell q
      let loc := fun q ↦ localCellVolume fine cell q
      let selected := (highCells mass loc K).filter fun q ↦
        cubeBucket (dominanceCutoff mass K)
          (cubeExponent (a := Fin C.centers.card) K) (loc q) = n
      let finalFine := restrictToCells fine cell hcell selected
      let finalCoarse := restrictToCells frozenCoarse cell hcell selected
      let w := 2 ^ n * dominanceCutoff mass K
      fine.shadingMass ≤
          (2 * (cubeExponent (a := Fin C.centers.card) K + 1)) •
            finalFine.shadingMass ∧
        finalFine.shadedUnion ⊆ finalCoarse.shadedUnion ∧
        finalFine.shadingMass ≤ K • finalCoarse.shadingMass ∧
        D ≤ (2 * (cubeExponent (a := Fin C.centers.card) K + 1)) •
          (K • finalCoarse.shadingMass) ∧
        (∀ q ∈ selected,
          w ≤ localCellVolume finalFine cell q ∧
            localCellVolume finalFine cell q < 2 * w) ∧
        ∀ x ∈ finalCoarse.shadedUnion,
          (w : ℝ≥0∞) ≤ volume (finalFine.shadedUnion ∩
            Metric.ball x (rho : ℝ)) ∧
          volume (finalFine.shadedUnion ∩ Metric.ball x (rho : ℝ)) ≤
            2000 * (w : ℝ≥0∞) := by
  obtain ⟨n, hn, hmaster⟩ := exists_common_weightedPackingLevel
    fine frozenCoarse hA C (by positivity) hFineA K hK hpoint hpositive
      hcover D hD
  refine ⟨n, hn, ?_⟩
  dsimp only at hmaster ⊢
  rcases hmaster with ⟨hretain, hfinalCover, hmass, hDfinal, hcellBand⟩
  refine ⟨hretain, hfinalCover, hmass, hDfinal, hcellBand, ?_⟩
  let cell := packingCellFin C
  let hcell := measurableSet_packingCellFin hA C
  let mass := fun q ↦ cellMass fine cell hcell q
  let loc := fun q ↦ localCellVolume fine cell q
  let selected := (highCells mass loc K).filter fun q ↦
    cubeBucket (dominanceCutoff mass K)
      (cubeExponent (a := Fin C.centers.card) K) (loc q) = n
  let finalFine := restrictToCells fine cell hcell selected
  let finalCoarse := restrictToCells frozenCoarse cell hcell selected
  let w := 2 ^ n * dominanceCutoff mass K
  have hcellBandENN : ∀ q ∈ selected,
      (w : ℝ≥0∞) ≤ volume (finalFine.shadedUnion ∩ cell q) ∧
        volume (finalFine.shadedUnion ∩ cell q) < 2 * (w : ℝ≥0∞) := by
    intro q hq
    have hqband := hcellBand q hq
    constructor
    · simpa [w, finalFine, cell] using
        (ENNReal.coe_le_coe.mpr hqband.1)
    · simpa [w, finalFine, cell] using
        (ENNReal.coe_lt_coe.mpr hqband.2)
  have hexact := exactRadius_band_of_cellBand C hrho selected
    finalFine.shadedUnion (w : ℝ≥0∞) hcellBandENN
  intro x hx
  have hxregion : x ∈ selectedRegion cell selected := by
    change x ∈ (restrictToCells frozenCoarse cell hcell selected).shadedUnion at hx
    rw [restrictToCells_shadedUnion] at hx
    exact hx.2
  have hxband := hexact x hxregion
  simpa [w, NNReal.coe_mul, NNReal.coe_pow, finalFine, cell,
    restrictToCells_shadedUnion,
    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hxband

end CubeWeightExactRadiusMaster

end

end Submission.Kakeya.ConvexFactoring

#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightExactRadiusMaster.exists_packingCertificate_of_isCompact
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightExactRadiusMaster.exists_finiteFamily_halfRadius_packingCertificate
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightExactRadiusMaster.exists_halfRadius_packingCertificate
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightExactRadiusMaster.exists_common_weightedPackingLevel_exactRadius
