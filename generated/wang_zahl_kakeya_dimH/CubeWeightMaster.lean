import BallwiseLocalVolumeUniformization
import CubeWeightUniformization

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open BallwiseLocalVolumeUniformization
open CubeWeightUniformization

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace CubeWeightMaster

def packingCellFin {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (q : Fin C.centers.card) : Set Space :=
  packingCell C q.1

theorem measurableSet_packingCellFin
    {A : Set Space} (hA : MeasurableSet A) {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (q : Fin C.centers.card) :
    MeasurableSet (packingCellFin C q) :=
  measurableSet_packingCell hA C q.1

theorem packingCellFin_pairwiseDisjoint
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) :
    Set.PairwiseDisjoint Set.univ (packingCellFin C) := by
  intro q hq r hr hqr
  exact packingCell_pairwiseDisjoint C (Set.mem_univ q.1)
    (Set.mem_univ r.1) (fun h ↦ hqr (Fin.ext h))

theorem iUnion_packingCellFin_eq
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho) :
    ⋃ q : Fin C.centers.card, packingCellFin C q = A := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    exact hxq.1
  · intro x hx
    have hxcover : x ∈ ⋃ j ∈ validCenterIndices C, packingCell C j := by
      rw [biUnion_valid_packingCell_eq C hrho]
      exact hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxcover
    obtain ⟨hj, hxcell⟩ := Set.mem_iUnion.mp hxj
    exact Set.mem_iUnion.mpr ⟨⟨j, Finset.mem_range.mp hj⟩, hxcell⟩

theorem packing_sum_cellMass_eq_shadingMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F)
    {A : Set Space} (hA : MeasurableSet A) {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
    (hYA : Y.shadedUnion ⊆ A) :
    ∑ q, cellMass Y (packingCellFin C)
        (measurableSet_packingCellFin hA C) q = Y.shadingMass.toNNReal := by
  apply sum_cellMass_eq_shadingMass_toNNReal
    Y (packingCellFin C) (measurableSet_packingCellFin hA C)
      (packingCellFin_pairwiseDisjoint C)
  simpa [iUnion_packingCellFin_eq C hrho] using hYA

theorem cellMass_restrictToCells
    {a ι : Type*} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι] {F : ConvexFamily ι}
    (Y : Shading F) (cell : a → Set Space)
    (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (selected : Finset a) (q : a) :
    cellMass (restrictToCells Y cell hcell selected) cell hcell q =
      if q ∈ selected then cellMass Y cell hcell q else 0 := by
  by_cases hq : q ∈ selected
  · rw [if_pos hq]
    apply ENNReal.coe_injective
    rw [coe_cellMass, coe_cellMass]
    unfold Shading.shadingMass
    apply Finset.sum_congr rfl
    intro i hi
    simp only [restrictToCells_carrier, Shading.restrictSet_carrier]
    congr 1
    ext x
    simp only [Set.mem_inter_iff]
    constructor
    · exact fun hx ↦ ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, cell_subset_selectedRegion cell selected hq hx.2⟩, hx.2⟩
  · rw [if_neg hq]
    apply ENNReal.coe_injective
    rw [coe_cellMass]
    change ((restrictToCells Y cell hcell selected).restrictSet
      (cell q) (hcell q)).shadingMass = 0
    unfold Shading.shadingMass
    apply Finset.sum_eq_zero
    intro i hi
    simp only [restrictToCells_carrier, Shading.restrictSet_carrier]
    suffices (Y.carrier i ∩ selectedRegion cell selected) ∩ cell q = ∅ by
      simp [this]
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx.1.2
      obtain ⟨hp, hxpcell⟩ := Set.mem_iUnion.mp hxp
      have hpq : p ≠ q := fun hpq ↦ hq (hpq ▸ hp)
      exact (Set.disjoint_left.mp
        (hdisj (Set.mem_univ p) (Set.mem_univ q) hpq) hxpcell hx.2).elim
    · exact Set.empty_subset _

theorem restrictToCells_shadingMass_toNNReal_eq_sum_cellMass
    {a ι : Type*} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι] {F : ConvexFamily ι}
    (Y : Shading F) (cell : a → Set Space)
    (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (selected : Finset a) :
    (restrictToCells Y cell hcell selected).shadingMass.toNNReal =
      ∑ q ∈ selected, cellMass Y cell hcell q := by
  let Z := restrictToCells Y cell hcell selected
  have hcover : Z.shadedUnion ⊆ ⋃ q, cell q := by
    intro x hx
    change x ∈ (restrictToCells Y cell hcell selected).shadedUnion at hx
    rw [restrictToCells_shadedUnion] at hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx.2
    obtain ⟨hq, hxcell⟩ := Set.mem_iUnion.mp hxq
    exact Set.mem_iUnion.mpr ⟨q, hxcell⟩
  have hsum := sum_cellMass_eq_shadingMass_toNNReal Z cell hcell hdisj hcover
  calc
    Z.shadingMass.toNNReal = ∑ q, cellMass Z cell hcell q := hsum.symm
    _ = ∑ q, if q ∈ selected then cellMass Y cell hcell q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simpa [Z] using cellMass_restrictToCells Y cell hcell hdisj selected q
    _ = ∑ q ∈ selected, cellMass Y cell hcell q := by simp


/-- Every finite shading union has volume at most its shading mass. -/
theorem volume_shadedUnion_le_shadingMass
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι} (Y : Shading F) :
    volume Y.shadedUnion ≤ Y.shadingMass := by
  change volume (⋃ i, Y.carrier i) ≤ ∑ i, volume (Y.carrier i)
  exact measure_iUnion_fintype_le volume _

/-- A pointwise multiplicity cap on the fine shading, together with a cover by
the same frozen coarse object, gives a division-free density lower bound for
that very object.  The multiplicity factor is unavoidable from these inputs. -/
theorem fineMass_le_nsmul_frozenCoarseMass
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (fine : Shading F) (frozenCoarse : Shading W) (K : ℕ)
    (hpoint : ∀ x, fine.pointMultiplicity x ≤ K)
    (hcover : fine.shadedUnion ⊆ frozenCoarse.shadedUnion) :
    fine.shadingMass ≤ K • frozenCoarse.shadingMass := by
  calc
    fine.shadingMass ≤ K • volume fine.shadedUnion :=
      FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
          fine K hpoint
    _ ≤ K • volume frozenCoarse.shadedUnion :=
      nsmul_le_nsmul_right (measure_mono hcover) K
    _ ≤ K • frozenCoarse.shadingMass :=
      nsmul_le_nsmul_right (volume_shadedUnion_le_shadingMass frozenCoarse) K

/-- Moving the center of a ball by less than `r` enlarges a radius-`s` ball
by at most `r`; this is the only metric input in the arbitrary-point bridge. -/
theorem ball_subset_ball_add_radius {c x : Space} {r s : ℝ}
    (hx : x ∈ Metric.ball c r) :
    Metric.ball x s ⊆ Metric.ball c (r + s) := by
  intro y hy
  rw [Metric.mem_ball] at hx hy ⊢
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
    _ < s + r := add_lt_add hy hx
    _ = r + s := add_comm _ _

/-- The reverse center move, again with exactly the additive radius loss. -/
theorem ball_subset_ball_add_radius_rev {c x : Space} {r s : ℝ}
    (hx : x ∈ Metric.ball c r) :
    Metric.ball c s ⊆ Metric.ball x (r + s) := by
  intro y hy
  rw [Metric.mem_ball] at hx hy ⊢
  calc
    dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
    _ < s + r := add_lt_add hy (by simpa [dist_comm] using hx)
    _ = r + s := add_comm _ _

/-- Every point of the finite packing cell lies in the radius-`rho` ball
centered at that cells enumerated packing center. -/
theorem packingCellFin_subset_centerBall
    {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (q : Fin C.centers.card) :
    packingCellFin C q ⊆
      Metric.ball (packingCenterAt C q.1) (rho : ℝ) := by
  intro x hx
  have hpiece : x ∈ packingCoverPiece C q.1 :=
    disjointed_subset (packingCoverPiece C) q.1 hx.2
  simpa [packingCoverPiece, q.2] using hpiece

/-- For a point owned by a radius-`rho` packing cell, a center statistic at
radius `2 rho` controls the point statistic at radius `rho` and is controlled
by the point statistic at radius `3 rho`. -/
theorem arbitraryPoint_one_two_three_volume_bridge
    (U : Set Space) {c x : Space} {rho : ℝ≥0}
    (hx : x ∈ Metric.ball c (rho : ℝ)) :
    volume (U ∩ Metric.ball x (rho : ℝ)) ≤
        volume (U ∩ Metric.ball c (2 * (rho : ℝ))) ∧
      volume (U ∩ Metric.ball c (2 * (rho : ℝ))) ≤
        volume (U ∩ Metric.ball x (3 * (rho : ℝ))) := by
  constructor
  · apply measure_mono
    exact inter_subset_inter_right _ (by
      simpa [two_mul] using
        (ball_subset_ball_add_radius (r := (rho : ℝ))
          (s := (rho : ℝ)) hx))
  · apply measure_mono
    exact inter_subset_inter_right _ (by
      have hr : (rho : ℝ) + 2 * (rho : ℝ) = 3 * (rho : ℝ) := by ring
      simpa only [hr] using
        (ball_subset_ball_add_radius_rev (r := (rho : ℝ))
          (s := 2 * (rho : ℝ)) hx))

/-- A half-open center bucket transfers to an arbitrary owned point only with
the honest `rho`/`3 rho` radius loss. -/
theorem arbitraryPoint_bucket_bridge
    (U : Set Space) {c x : Space} {rho : ℝ≥0} {w : ℝ≥0∞}
    (hx : x ∈ Metric.ball c (rho : ℝ))
    (hcenter : w ≤ volume (U ∩ Metric.ball c (2 * (rho : ℝ))) ∧
      volume (U ∩ Metric.ball c (2 * (rho : ℝ))) < 2 * w) :
    volume (U ∩ Metric.ball x (rho : ℝ)) < 2 * w ∧
      w ≤ volume (U ∩ Metric.ball x (3 * (rho : ℝ))) := by
  obtain ⟨hleft, hright⟩ := arbitraryPoint_one_two_three_volume_bridge U hx
  exact ⟨hleft.trans_lt hcenter.2, hcenter.1.trans hright⟩
/-- Direct packing-cell-to-arbitrary-point form of the `rho`/`2rho`/`3rho`
volume comparison. -/
theorem packingCellFin_point_volume_bridge
    (U : Set Space) {A : Set Space} {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (q : Fin C.centers.card)
    {x : Space} (hx : x ∈ packingCellFin C q) :
    volume (U ∩ Metric.ball x (rho : ℝ)) ≤
        volume (U ∩ Metric.ball (packingCenterAt C q.1)
          (2 * (rho : ℝ))) ∧
      volume (U ∩ Metric.ball (packingCenterAt C q.1)
          (2 * (rho : ℝ))) ≤
        volume (U ∩ Metric.ball x (3 * (rho : ℝ))) :=
  arbitraryPoint_one_two_three_volume_bridge U
    (packingCellFin_subset_centerBall C q hx)


theorem localCellVolume_le_shadingMass_toNNReal
    {a ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ConvexFamily ι} (Y : Shading F)
    (cell : a → Set Space) (q : a) :
    localCellVolume Y cell q ≤ Y.shadingMass.toNNReal := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_localCellVolume, ENNReal.coe_toNNReal (shadingMass_ne_top Y)]
  exact (measure_mono inter_subset_left).trans
    (volume_shadedUnion_le_shadingMass Y)

theorem localCellVolume_le_sum_cellMass
    {a ι : Type*} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι] {F : ConvexFamily ι}
    (Y : Shading F) (cell : a → Set Space)
    (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (hcover : Y.shadedUnion ⊆ ⋃ q, cell q) (q : a) :
    localCellVolume Y cell q ≤ ∑ p, cellMass Y cell hcell p := by
  rw [sum_cellMass_eq_shadingMass_toNNReal Y cell hcell hdisj hcover]
  exact localCellVolume_le_shadingMass_toNNReal Y cell q
/-- Master finite-cell output: one common spatial restriction supplies the
polylogarithmic fine-mass retention, the literal half-open local-volume bucket,
the final fine-to-frozen-coarse cover, and a density lower bound for that same
frozen coarse shading.  `D` packages whatever item-2 numerator was already
known to lie below the input fine mass. -/
theorem exists_common_weightedCellLevel
    {a ι κ : Type*} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (fine : Shading F) (frozenCoarse : Shading W)
    (cell : a → Set Space) (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (hcellCover : fine.shadedUnion ⊆ ⋃ q, cell q)
    (K : ℕ) (hK : 0 < K)
    (hpoint : ∀ x, fine.pointMultiplicity x ≤ K)
    (hpositive : 0 < fine.shadingMass.toNNReal)
    (hcover : fine.shadedUnion ⊆ frozenCoarse.shadedUnion)
    (D : ℝ≥0∞) (hD : D ≤ fine.shadingMass) :
    ∃ n, n ≤ cubeExponent (a := a) K ∧
      let mass := fun q ↦ cellMass fine cell hcell q
      let loc := fun q ↦ localCellVolume fine cell q
      let selected := (highCells mass loc K).filter fun q ↦
        cubeBucket (dominanceCutoff mass K)
          (cubeExponent (a := a) K) (loc q) = n
      let finalFine := restrictToCells fine cell hcell selected
      let finalCoarse := restrictToCells frozenCoarse cell hcell selected
      fine.shadingMass ≤
          (2 * (cubeExponent (a := a) K + 1)) • finalFine.shadingMass ∧
        finalFine.shadedUnion ⊆ finalCoarse.shadedUnion ∧
        finalFine.shadingMass ≤ K • finalCoarse.shadingMass ∧
        D ≤ (2 * (cubeExponent (a := a) K + 1)) •
          (K • finalCoarse.shadingMass) ∧
        ∀ q ∈ selected,
          let w := 2 ^ n * dominanceCutoff mass K
          w ≤ localCellVolume finalFine cell q ∧
            localCellVolume finalFine cell q < 2 * w := by
  let mass := fun q ↦ cellMass fine cell hcell q
  let loc := fun q ↦ localCellVolume fine cell q
  have hdom : ∀ q, mass q ≤ K * loc q := by
    intro q
    simpa [mass, loc] using
      cellMass_le_mul_localCellVolume fine cell hcell K hpoint q
  have htotal : 0 < ∑ q, mass q := by
    rw [show (∑ q, mass q) = fine.shadingMass.toNNReal by
      simpa [mass] using
        sum_cellMass_eq_shadingMass_toNNReal
          fine cell hcell hdisj hcellCover]
    exact hpositive
  have hloc : ∀ q, loc q ≤ ∑ p, mass p := by
    intro q
    simpa [mass, loc] using
      localCellVolume_le_sum_cellMass
        fine cell hcell hdisj hcellCover q
  obtain ⟨n, hn, hretainNN, hband⟩ :=
    exists_weightedCubeLevel mass loc K hK hdom htotal hloc
  refine ⟨n, hn, ?_⟩
  dsimp only
  let selected := (highCells mass loc K).filter fun q ↦
    cubeBucket (dominanceCutoff mass K)
      (cubeExponent (a := a) K) (loc q) = n
  let finalFine := restrictToCells fine cell hcell selected
  let finalCoarse := restrictToCells frozenCoarse cell hcell selected
  have hinputSum : (∑ q, mass q) = fine.shadingMass.toNNReal := by
    simpa [mass] using sum_cellMass_eq_shadingMass_toNNReal
      fine cell hcell hdisj hcellCover
  have hselectedSum : finalFine.shadingMass.toNNReal =
      ∑ q ∈ selected, mass q := by
    simpa [finalFine, mass] using
      restrictToCells_shadingMass_toNNReal_eq_sum_cellMass
        fine cell hcell hdisj selected
  have hretainNN2 : fine.shadingMass.toNNReal ≤
      (2 * (cubeExponent (a := a) K + 1)) •
        finalFine.shadingMass.toNNReal := by
    rw [← hinputSum, hselectedSum]
    simpa [selected] using hretainNN
  have hretain : fine.shadingMass ≤
      (2 * (cubeExponent (a := a) K + 1)) •
        finalFine.shadingMass := by
    calc
      fine.shadingMass = (fine.shadingMass.toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal (shadingMass_ne_top fine)).symm
      _ ≤ (((2 * (cubeExponent (a := a) K + 1)) •
          finalFine.shadingMass.toNNReal : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr hretainNN2
      _ = (2 * (cubeExponent (a := a) K + 1)) •
          finalFine.shadingMass := by
        simp [nsmul_eq_mul, ENNReal.coe_toNNReal (shadingMass_ne_top finalFine)]
  have hfinalCover : finalFine.shadedUnion ⊆ finalCoarse.shadedUnion := by
    simpa [finalFine, finalCoarse] using
      commonCellRestriction_preserves_cover
        fine frozenCoarse cell hcell selected hcover
  have hfinalPoint : ∀ x, finalFine.pointMultiplicity x ≤ K := by
    intro x
    simp only [finalFine, restrictToCells, Shading.pointMultiplicity_restrictSet]
    split_ifs
    · exact hpoint x
    · exact Nat.zero_le _
  have hsameObject : finalFine.shadingMass ≤
      K • finalCoarse.shadingMass :=
    fineMass_le_nsmul_frozenCoarseMass
      finalFine finalCoarse K hfinalPoint hfinalCover
  refine ⟨hretain, hfinalCover, hsameObject, ?_, ?_⟩
  · exact hD.trans (hretain.trans
      (nsmul_le_nsmul_right hsameObject
        (2 * (cubeExponent (a := a) K + 1))))
  · intro q hq
    have hlocEq : localCellVolume finalFine cell q = loc q := by
      unfold localCellVolume
      rw [show finalFine = restrictToCells fine cell hcell selected by rfl]
      rw [restrictToCells_local_eq fine cell hcell selected hq]
      rfl
    have hhalf := inDyadicBand_halfOpen
      (hband q (by simpa [selected] using hq))
    change (2 ^ n * dominanceCutoff mass K ≤
      localCellVolume finalFine cell q ∧
      localCellVolume finalFine cell q <
        2 * (2 ^ n * dominanceCutoff mass K))
    rw [hlocEq]
    exact hhalf

/-- Ballwise specialization of the master theorem.  The packing certificate is
kept explicit: global existence for a union of tubes is a separate compactness
input, while Ballwise already constructs it for a subset of one tube. -/
theorem exists_common_weightedPackingLevel
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (fine : Shading F) (frozenCoarse : Shading W)
    {A : Set Space} (hA : MeasurableSet A) {rho : ℝ≥0}
    (C : PackingCertificate A (rho / 3)) (hrho : 0 < rho)
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
      fine.shadingMass ≤
          (2 * (cubeExponent (a := Fin C.centers.card) K + 1)) •
            finalFine.shadingMass ∧
        finalFine.shadedUnion ⊆ finalCoarse.shadedUnion ∧
        finalFine.shadingMass ≤ K • finalCoarse.shadingMass ∧
        D ≤ (2 * (cubeExponent (a := Fin C.centers.card) K + 1)) •
          (K • finalCoarse.shadingMass) ∧
        ∀ q ∈ selected,
          let w := 2 ^ n * dominanceCutoff mass K
          w ≤ localCellVolume finalFine cell q ∧
            localCellVolume finalFine cell q < 2 * w := by
  apply exists_common_weightedCellLevel
    fine frozenCoarse (packingCellFin C)
      (measurableSet_packingCellFin hA C)
      (packingCellFin_pairwiseDisjoint C)
      ?_ K hK hpoint hpositive hcover D hD
  simpa [iUnion_packingCellFin_eq C hrho] using hFineA


end CubeWeightMaster

end

end Submission.Kakeya.ConvexFactoring
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightMaster.packing_sum_cellMass_eq_shadingMass
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightMaster.restrictToCells_shadingMass_toNNReal_eq_sum_cellMass
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightMaster.fineMass_le_nsmul_frozenCoarseMass
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightMaster.arbitraryPoint_bucket_bridge
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightMaster.exists_common_weightedCellLevel
#print axioms Submission.Kakeya.ConvexFactoring.CubeWeightMaster.exists_common_weightedPackingLevel
