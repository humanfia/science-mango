import Submission.Kakeya.ConvexFactoring.Factorization
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement

open scoped ENNReal NNReal
open MeasureTheory Set

/-!
# Heavy-parent selection

This module turns an average active-fine density bound into a parentwise
density witness. Heavy parents retain at least half of the active shaded
mass, and a subsequent finite label pigeonhole loses only the number of
labels. The global loss parameter enters the heavy threshold and pointwise
witness, but not the bucket-retention factor. It also provides active coarse
families and shadings for downstream geometric estimates.
-/


namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section


namespace HeavyParentSelection


local instance heavyParentSelectionPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- `D_k`: summed fine-body volume in the actual factorization fiber over `k`. -/
def fiberBodyMass (P : ConvexFactorization F W) (k : κ) : ℝ≥0∞ :=
  ∑ i ∈ P.index.fiber k, volume (F i : Set Space)

/-- `M_k`: multiplicity-counted shaded mass in the actual fiber over `k`. -/
def fiberShadingMass (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) : ℝ≥0∞ :=
  ∑ i ∈ P.index.fiber k, volume (Y.carrier i)

/-- `D`: summed body mass over the active fine carrier. -/
def activeBodyMass (P : ConvexFactorization F W) : ℝ≥0∞ :=
  ∑ i ∈ P.index.fine, volume (F i : Set Space)

/-- `M`: multiplicity-counted shading mass over the active fine carrier. -/
def activeShadingMass (P : ConvexFactorization F W)
    (Y : Shading F) : ℝ≥0∞ :=
  ∑ i ∈ P.index.fine, volume (Y.carrier i)

/-- Active fine-body mass is the sum of the body masses of the actual fibers. -/
theorem activeBodyMass_eq_sum_fiberBodyMass
    (P : ConvexFactorization F W) :
    activeBodyMass P =
      ∑ k ∈ P.index.coarse, fiberBodyMass P k := by
  simpa [activeBodyMass, fiberBodyMass] using
    P.index.sum_fiberwise (fun i => volume (F i : Set Space))

/-- Active multiplicity-counted shaded mass is the sum of the corresponding
fiber masses. -/
theorem activeShadingMass_eq_sum_fiberShadingMass
    (P : ConvexFactorization F W) (Y : Shading F) :
    activeShadingMass P Y =
      ∑ k ∈ P.index.coarse, fiberShadingMass P Y k := by
  simpa [activeShadingMass, fiberShadingMass] using
    P.index.sum_fiberwise (fun i => volume (Y.carrier i))

/-- Every fine-body fiber mass is finite. -/
theorem fiberBodyMass_ne_top (P : ConvexFactorization F W) (k : κ) :
    fiberBodyMass P k ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (F i).isCompact.measure_lt_top.ne

/-- Every fine-shading fiber mass is finite. -/
theorem fiberShadingMass_ne_top (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) : fiberShadingMass P Y k ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (shadingPiece_volume_lt_top Y i).ne

/-- The active fine-body mass is finite. -/
theorem activeBodyMass_ne_top (P : ConvexFactorization F W) :
    activeBodyMass P ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (F i).isCompact.measure_lt_top.ne

/-- The active multiplicity-counted shaded mass is finite. -/
theorem activeShadingMass_ne_top (P : ConvexFactorization F W)
    (Y : Shading F) : activeShadingMass P Y ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro i hi
  exact (shadingPiece_volume_lt_top Y i).ne

/-- A parent is heavy when its body/shading cross inequality is no worse than
twice the global loss `L`. -/
def heavyParents (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) : Finset κ :=
  P.index.coarse.filter fun k =>
    lambda * fiberBodyMass P k ≤
      (2 * L) * fiberShadingMass P Y k

/-- The complementary light parents. -/
def lightParents (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) : Finset κ :=
  P.index.coarse.filter fun k =>
    ¬ lambda * fiberBodyMass P k ≤
      (2 * L) * fiberShadingMass P Y k

/-- `M_good`: shaded mass over the heavy parent fibers. -/
def heavyShadingMass (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ k ∈ heavyParents P Y lambda L, fiberShadingMass P Y k

/-- Shaded mass over the complementary light parent fibers. -/
def lightShadingMass (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ k ∈ lightParents P Y lambda L, fiberShadingMass P Y k

/-- Body mass over the complementary light parent fibers. -/
def lightBodyMass (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ k ∈ lightParents P Y lambda L, fiberBodyMass P k

/-- Heavy and light parent fibers partition the active shaded mass. -/
theorem heavy_add_light_shadingMass
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) :
    heavyShadingMass P Y lambda L + lightShadingMass P Y lambda L =
      activeShadingMass P Y := by
  rw [activeShadingMass_eq_sum_fiberShadingMass]
  simpa [heavyShadingMass, lightShadingMass, heavyParents, lightParents] using
    (Finset.sum_filter_add_sum_filter_not P.index.coarse
      (fun k => lambda * fiberBodyMass P k ≤
        (2 * L) * fiberShadingMass P Y k)
      (fiberShadingMass P Y))

/-- The shaded mass carried by light parents is finite. -/
theorem lightShadingMass_ne_top
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) : lightShadingMass P Y lambda L ≠ ∞ := by
  apply ENNReal.sum_ne_top.2
  intro k hk
  exact fiberShadingMass_ne_top P Y k

/-- Heavy-parent selection. If `lambda * D ≤ L * M`, then heavy fibers carry
at least half of `M`, equivalently `M ≤ 2 * M_good`.

The hypotheses `L ≠ 0` and `L ≠ ∞` are exactly those used to cancel `L` in
`ℝ≥0∞`; no cancellation of `lambda` is used. -/
theorem activeShadingMass_le_two_mul_heavyShadingMass
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hglobal : lambda * activeBodyMass P ≤ L * activeShadingMass P Y) :
    activeShadingMass P Y ≤ 2 * heavyShadingMass P Y lambda L := by
  have hlightPiece : ∀ k ∈ lightParents P Y lambda L,
      (2 * L) * fiberShadingMass P Y k ≤
        lambda * fiberBodyMass P k := by
    intro k hk
    have hnot := (Finset.mem_filter.mp hk).2
    exact (le_of_lt (lt_of_not_ge hnot))
  have hlightCross :
      (2 * L) * lightShadingMass P Y lambda L ≤
        lambda * lightBodyMass P Y lambda L := by
    rw [lightShadingMass, lightBodyMass, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hlightPiece k hk
  have hlightBody : lightBodyMass P Y lambda L ≤ activeBodyMass P := by
    rw [activeBodyMass_eq_sum_fiberBodyMass]
    unfold lightBodyMass
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hbeforeCancel :
      (2 * lightShadingMass P Y lambda L) * L ≤
        activeShadingMass P Y * L := by
    calc
      (2 * lightShadingMass P Y lambda L) * L =
          (2 * L) * lightShadingMass P Y lambda L := by ac_rfl
      _ ≤ lambda * lightBodyMass P Y lambda L := hlightCross
      _ ≤ lambda * activeBodyMass P := mul_le_mul' le_rfl hlightBody
      _ ≤ L * activeShadingMass P Y := hglobal
      _ = activeShadingMass P Y * L := mul_comm _ _
  have htwiceLight :
      2 * lightShadingMass P Y lambda L ≤ activeShadingMass P Y :=
    (ENNReal.mul_le_mul_iff_left hL0 hLtop).mp hbeforeCancel
  have hlightLeHeavy :
      lightShadingMass P Y lambda L ≤ heavyShadingMass P Y lambda L := by
    apply (ENNReal.add_le_add_iff_right
      (lightShadingMass_ne_top P Y lambda L)).mp
    calc
      lightShadingMass P Y lambda L + lightShadingMass P Y lambda L =
          2 * lightShadingMass P Y lambda L := by simp [two_mul]
      _ ≤ activeShadingMass P Y := htwiceLight
      _ = heavyShadingMass P Y lambda L +
          lightShadingMass P Y lambda L :=
        (heavy_add_light_shadingMass P Y lambda L).symm
  rw [← heavy_add_light_shadingMass P Y lambda L]
  calc
    heavyShadingMass P Y lambda L + lightShadingMass P Y lambda L ≤
        heavyShadingMass P Y lambda L + heavyShadingMass P Y lambda L :=
      add_le_add_right hlightLeHeavy _
    _ = 2 * heavyShadingMass P Y lambda L := by simp [two_mul]

/-- A selected parent set admits one fine witness per parent. -/
def HasDenseFiberWitness (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) (lambda loss : ℝ≥0∞) : Prop :=
  ∀ k ∈ parents, ∃ i ∈ P.index.fiber k,
    lambda * volume (F i : Set Space) ≤
      loss * volume (Y.carrier i)

/-- Uniform fine density immediately supplies a witness on every active
parent, using only nonemptiness of each active fiber. -/
theorem hasDenseFiberWitness_of_uniform
    (P : ConvexFactorization F W) (Y : Shading F) (lambda : ℝ≥0∞)
    (hfiber : ∀ k ∈ P.index.coarse, (P.index.fiber k).Nonempty)
    (huniform : ∀ i ∈ P.index.fine,
      lambda * volume (F i : Set Space) ≤ volume (Y.carrier i)) :
    HasDenseFiberWitness P Y P.index.coarse lambda 1 := by
  intro k hk
  obtain ⟨i, hi⟩ := hfiber k hk
  refine ⟨i, hi, ?_⟩
  simpa using huniform i (P.index.fiber_subset_fine k hi)

/-- Every heavy parent has a fine witness with loss `2 * L`. This is the
finite weighted-average step inside a parent fiber. -/
theorem heavyParents_hasDenseFiberWitness
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞)
    (hfiber : ∀ k ∈ P.index.coarse, (P.index.fiber k).Nonempty) :
    HasDenseFiberWitness P Y (heavyParents P Y lambda L) lambda (2 * L) := by
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  have hsum :
      (∑ i ∈ P.index.fiber k,
        lambda * volume (F i : Set Space)) ≤
      ∑ i ∈ P.index.fiber k,
        (2 * L) * volume (Y.carrier i) := by
    simpa [fiberBodyMass, fiberShadingMass, Finset.mul_sum] using hk'.2
  exact ENNReal.exists_le_of_sum_le (hfiber k hk'.1) hsum

/-- Generic finite parent-label weighted pigeonhole, stated directly in
`ℝ≥0∞`. No nonzero or finite-weight side condition is needed. -/
theorem exists_parentLabel_weightedBucket
    {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]
    (s : Finset κ) (label : κ → β) (weight : κ → ℝ≥0∞) :
    ∃ b : β,
      (∑ k ∈ s, weight k) ≤
        Fintype.card β •
          ∑ k ∈ dyadicFiber s label b, weight k := by
  classical
  let bucketWeight : β → ℝ≥0∞ := fun b =>
    ∑ k ∈ dyadicFiber s label b, weight k
  obtain ⟨b, _hb, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset β) bucketWeight
      (Finset.univ_nonempty : (Finset.univ : Finset β).Nonempty)
  refine ⟨b, ?_⟩
  calc
    (∑ k ∈ s, weight k) =
        ∑ b' ∈ (Finset.univ : Finset β), bucketWeight b' := by
      change (∑ k ∈ s, weight k) =
        ∑ b' ∈ (Finset.univ : Finset β),
          ∑ k ∈ s with label k = b', weight k
      exact (Finset.sum_fiberwise_of_maps_to
        (s := s) (t := (Finset.univ : Finset β)) (g := label)
        (fun k hk => Finset.mem_univ (label k)) weight).symm
    _ ≤ (Finset.univ : Finset β).card • bucketWeight b :=
      Finset.sum_le_card_nsmul (Finset.univ : Finset β) bucketWeight
        (bucketWeight b) (fun b' hb' => hmax b' hb')
    _ = Fintype.card β •
        ∑ k ∈ dyadicFiber s label b, weight k := by
      simp [bucketWeight]

/-- Specialization of the generic bucket theorem to the heavy-parent shaded
masses. The bucket count is the only additional loss. -/
theorem exists_heavyParentLabel_bucket
    {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) (label : κ → β) :
    ∃ b : β,
      heavyShadingMass P Y lambda L ≤
        Fintype.card β •
          (∑ k ∈ dyadicFiber (heavyParents P Y lambda L) label b,
            fiberShadingMass P Y k) := by
  simpa [heavyShadingMass] using
    exists_parentLabel_weightedBucket
      (heavyParents P Y lambda L) label (fiberShadingMass P Y)

/-- Heavy selection followed by one finite parent-label bucket retains the
entire active shaded mass within the explicit loss `2 * card β`. -/
theorem exists_heavyParentLabel_bucket_withinFactor
    {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) (label : κ → β)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hglobal : lambda * activeBodyMass P ≤ L * activeShadingMass P Y) :
    ∃ b : β,
      WithinFactor (2 * Fintype.card β) (activeShadingMass P Y)
        (∑ k ∈ dyadicFiber (heavyParents P Y lambda L) label b,
          fiberShadingMass P Y k) := by
  obtain ⟨b, hb⟩ :=
    exists_heavyParentLabel_bucket P Y lambda L label
  refine ⟨b, ?_⟩
  have hheavy : WithinFactor 2 (activeShadingMass P Y)
      (heavyShadingMass P Y lambda L) := by
    unfold WithinFactor
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      activeShadingMass_le_two_mul_heavyShadingMass
        P Y lambda L hL0 hLtop hglobal
  have hbucket : WithinFactor (Fintype.card β)
      (heavyShadingMass P Y lambda L)
      (∑ k ∈ dyadicFiber (heavyParents P Y lambda L) label b,
        fiberShadingMass P Y k) := hb
  exact WithinFactor.trans hheavy hbucket

omit [DecidableEq κ] in
/-- The coarse family restricted to an arbitrary selected finite index set. -/
def selectedCoarseFamily (W : ConvexFamily κ) (s : Finset κ) :
    ConvexFamily {k // k ∈ s} :=
  fun k => W k.1

omit [DecidableEq κ] in
/-- The selected coarse family evaluates to the original body at the
underlying coarse index. -/
@[simp] theorem selectedCoarseFamily_apply
    (W : ConvexFamily κ) (s : Finset κ) (k : {k // k ∈ s}) :
    selectedCoarseFamily W s k = W k.1 := rfl

omit [DecidableEq κ] in
/-- A coarse shading reindexed by an arbitrary selected finite index set. -/
def selectedCoarseShading {W : ConvexFamily κ} (Z : Shading W)
    (s : Finset κ) : Shading (selectedCoarseFamily W s) where
  carrier k := Z.carrier k.1
  measurable_carrier k := Z.measurable_carrier k.1
  carrier_subset k := Z.carrier_subset k.1

omit [DecidableEq κ] in
/-- The selected coarse shading has the original carrier at the underlying
coarse index. -/
@[simp] theorem selectedCoarseShading_carrier
    {W : ConvexFamily κ} (Z : Shading W) (s : Finset κ)
    (k : {k // k ∈ s}) :
    (selectedCoarseShading Z s).carrier k = Z.carrier k.1 := rfl

omit [DecidableEq κ] in
/-- The selected coarse subtype family volume is its original finite subsum. -/
theorem selectedCoarseFamily_volume
    (W : ConvexFamily κ) (s : Finset κ) :
    familyVolume (selectedCoarseFamily W s) =
      ∑ k ∈ s, volume (W k : Set Space) := by
  unfold familyVolume
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach s (fun k => volume (W k : Set Space))

omit [DecidableEq κ] in
/-- The selected coarse subtype shading mass is its original finite subsum. -/
theorem selectedCoarseShading_mass
    {W : ConvexFamily κ} (Z : Shading W) (s : Finset κ) :
    (selectedCoarseShading Z s).shadingMass =
      ∑ k ∈ s, volume (Z.carrier k) := by
  unfold Shading.shadingMass
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach s (fun k => volume (Z.carrier k))

/-- The genuinely active coarse family, indexed by `P.index.coarse`. -/
def activeCoarseFamily (P : ConvexFactorization F W) :
    ConvexFamily {k // k ∈ P.index.coarse} :=
  selectedCoarseFamily W P.index.coarse

/-- The active coarse family evaluates to its underlying coarse body. -/
@[simp] theorem activeCoarseFamily_apply
    (P : ConvexFactorization F W) (k : {k // k ∈ P.index.coarse}) :
    activeCoarseFamily P k = W k.1 := rfl

/-- A coarse shading restricted to the genuinely active coarse carrier. -/
def activeCoarseShading (P : ConvexFactorization F W) (Z : Shading W) :
    Shading (activeCoarseFamily P) :=
  selectedCoarseShading Z P.index.coarse

/-- The active coarse shading has the original carrier at the underlying
active coarse index. -/
@[simp] theorem activeCoarseShading_carrier
    (P : ConvexFactorization F W) (Z : Shading W)
    (k : {k // k ∈ P.index.coarse}) :
    (activeCoarseShading P Z).carrier k = Z.carrier k.1 := rfl

/-- The active coarse family volume is the active coarse-body subsum. -/
theorem activeCoarseFamily_volume (P : ConvexFactorization F W) :
    familyVolume (activeCoarseFamily P) =
      ∑ k ∈ P.index.coarse, volume (W k : Set Space) :=
  selectedCoarseFamily_volume W P.index.coarse

/-- The active coarse shading mass is the active carrier subsum. -/
theorem activeCoarseShading_mass
    (P : ConvexFactorization F W) (Z : Shading W) :
    (activeCoarseShading P Z).shadingMass =
      ∑ k ∈ P.index.coarse, volume (Z.carrier k) :=
  selectedCoarseShading_mass Z P.index.coarse

end HeavyParentSelection

end

end Submission.Kakeya.ConvexFactoring
