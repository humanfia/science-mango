import Submission.Kakeya.ConvexFactoring.FrameBoxVolume

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Transverse coordinate overlap

This module gives exact volume formulas for intersections cut out by three
independent inner-product coordinates in Euclidean three-space.  The Jacobian
is expressed by the determinant of the corresponding linear coordinate map.

The results here deliberately stop at this coordinate-level statement.  They
do not yet connect `FrameBox.carrier` to affine-slab constraints, nor do they
identify the determinant with an angle, sine, or scalar triple product.  Those
bridges are separate geometric inputs.
-/

namespace TransverseCoordinateOverlap

abbrev Coord := Fin 3 → ℝ

/-- The axis-aligned closed coordinate box in Euclidean three-space. -/
def euclideanIcc (lower upper : Coord) : Set Space :=
  (@WithLp.ofLp 2 Coord) ⁻¹' Set.Icc lower upper

/-- Product formula for an axis-aligned Euclidean coordinate box. -/
theorem volume_euclideanIcc (lower upper : Coord) :
    volume (euclideanIcc lower upper) =
      ∏ i, ENNReal.ofReal (upper i - lower i) := by
  rw [euclideanIcc,
    (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
      (measurableSet_Icc : MeasurableSet (Set.Icc lower upper)).nullMeasurableSet]
  exact Real.volume_Icc_pi

/-- The linear coordinate map whose rows are the three vectors `v i`. -/
def innerCoordinateMap (v : Fin 3 → Space) : Space →ₗ[ℝ] Space where
  toFun x := WithLp.toLp 2 (fun i ↦ ⟪v i, x⟫_ℝ)
  map_add' x y := by
    exact congrArg (WithLp.toLp 2) <| funext fun i ↦
      inner_add_right (v i) x y
  map_smul' c x := by
    exact congrArg (WithLp.toLp 2) <| funext fun i ↦
      inner_smul_right (v i) x c

@[simp] theorem innerCoordinateMap_apply (v : Fin 3 → Space) (x : Space) (i : Fin 3) :
    WithLp.ofLp (innerCoordinateMap v x) i = ⟪v i, x⟫_ℝ :=
  rfl

/-- The inverse image of a rectangular coordinate window. -/
def coordinateWindow (v : Fin 3 → Space) (lower upper : Coord) : Set Space :=
  innerCoordinateMap v ⁻¹' euclideanIcc lower upper

theorem mem_coordinateWindow_iff (v : Fin 3 → Space) (lower upper : Coord)
    (x : Space) :
    x ∈ coordinateWindow v lower upper ↔
      ∀ i, lower i ≤ ⟪v i, x⟫_ℝ ∧ ⟪v i, x⟫_ℝ ≤ upper i := by
  change lower ≤ (fun i ↦ ⟪v i, x⟫_ℝ) ∧
      (fun i ↦ ⟪v i, x⟫_ℝ) ≤ upper ↔ _
  constructor
  · rintro ⟨hlower, hupper⟩ i
    exact ⟨hlower i, hupper i⟩
  · intro h
    exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩

/-- Exact Jacobian formula for a three-coordinate window.  The determinant is
the genuine geometric transversality quantity of the three coordinate rows. -/
theorem volume_coordinateWindow (v : Fin 3 → Space) (lower upper : Coord)
    (hdet : LinearMap.det (innerCoordinateMap v) ≠ 0) :
    volume (coordinateWindow v lower upper) =
      ENNReal.ofReal |(LinearMap.det (innerCoordinateMap v))⁻¹| *
        ∏ i, ENNReal.ofReal (upper i - lower i) := by
  rw [coordinateWindow,
    volume.addHaar_preimage_linearMap hdet,
    volume_euclideanIcc]

/-- A possibly translated window with scalar centers and nonnegative half-widths. -/
def centeredCoordinateWindow (v : Fin 3 → Space) (center : Coord)
    (half : Fin 3 → ℝ≥0) : Set Space :=
  coordinateWindow v
    (fun i ↦ center i - (half i : ℝ))
    (fun i ↦ center i + (half i : ℝ))

theorem mem_centeredCoordinateWindow_iff (v : Fin 3 → Space) (center : Coord)
    (half : Fin 3 → ℝ≥0) (x : Space) :
    x ∈ centeredCoordinateWindow v center half ↔
      ∀ i, |⟪v i, x⟫_ℝ - center i| ≤ (half i : ℝ) := by
  rw [centeredCoordinateWindow, mem_coordinateWindow_iff]
  constructor
  · intro hx i
    rw [abs_le]
    constructor <;> linarith [hx i |>.1, hx i |>.2]
  · intro hx i
    have hi := hx i
    rw [abs_le] at hi
    constructor <;> linarith [hi.1, hi.2]

/-- Exact transverse-window volume: the three full widths are `2 * half i`. -/
theorem volume_centeredCoordinateWindow (v : Fin 3 → Space) (center : Coord)
    (half : Fin 3 → ℝ≥0)
    (hdet : LinearMap.det (innerCoordinateMap v) ≠ 0) :
    volume (centeredCoordinateWindow v center half) =
      ENNReal.ofReal |(LinearMap.det (innerCoordinateMap v))⁻¹| *
        ∏ i, (2 * (half i : ℝ≥0∞)) := by
  rw [centeredCoordinateWindow, volume_coordinateWindow v _ _ hdet]
  apply congrArg (fun z ↦ ENNReal.ofReal |(LinearMap.det (innerCoordinateMap v))⁻¹| * z)
  apply Finset.prod_congr rfl
  intro i _
  rw [show center i + (half i : ℝ) - (center i - (half i : ℝ)) =
      2 * (half i : ℝ) by ring]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
  norm_num

/-- Any measurable or nonmeasurable set constrained by three genuine linear
windows satisfies the corresponding determinant overlap bound. -/
theorem volume_le_of_subset_centeredCoordinateWindow
    (A : Set Space) (v : Fin 3 → Space) (center : Coord) (half : Fin 3 → ℝ≥0)
    (hdet : LinearMap.det (innerCoordinateMap v) ≠ 0)
    (hA : A ⊆ centeredCoordinateWindow v center half) :
    volume A ≤ ENNReal.ofReal |(LinearMap.det (innerCoordinateMap v))⁻¹| *
      ∏ i, (2 * (half i : ℝ≥0∞)) := by
  rw [← volume_centeredCoordinateWindow v center half hdet]
  exact measure_mono hA

/-- A closed affine slab described by a normal vector, a scalar center, and a
nonnegative half-width. -/
def affineSlab (normal : Space) (center : ℝ) (half : ℝ≥0) : Set Space :=
  {x | |⟪normal, x⟫_ℝ - center| ≤ (half : ℝ)}

/-- The actual intersection of two oriented slabs with a third longitudinal
cut is a three-coordinate window. -/
theorem inter_affineSlab_inter_affineSlab_inter_affineSlab
    (n₀ n₁ u : Space) (c₀ c₁ c₂ : ℝ) (h₀ h₁ h₂ : ℝ≥0) :
    affineSlab n₀ c₀ h₀ ∩ affineSlab n₁ c₁ h₁ ∩ affineSlab u c₂ h₂ =
      centeredCoordinateWindow ![n₀, n₁, u] ![c₀, c₁, c₂] ![h₀, h₁, h₂] := by
  ext x
  rw [mem_centeredCoordinateWindow_iff]
  simp only [Set.mem_inter_iff, affineSlab, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hn₀, hn₁⟩, hu⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

/-- Exact three-dimensional overlap formula for two oriented slabs after an
explicit longitudinal cut.  No overlap estimate is assumed: invertibility of
the displayed coordinate map is the transversality hypothesis. -/
theorem volume_twoSlabs_with_longitudinalCut
    (n₀ n₁ u : Space) (c₀ c₁ c₂ : ℝ) (h₀ h₁ h₂ : ℝ≥0)
    (hdet : LinearMap.det (innerCoordinateMap ![n₀, n₁, u]) ≠ 0) :
    volume (affineSlab n₀ c₀ h₀ ∩ affineSlab n₁ c₁ h₁ ∩ affineSlab u c₂ h₂) =
      ENNReal.ofReal |(LinearMap.det (innerCoordinateMap ![n₀, n₁, u]))⁻¹| *
        (2 * (h₀ : ℝ≥0∞)) * (2 * (h₁ : ℝ≥0∞)) * (2 * (h₂ : ℝ≥0∞)) := by
  rw [inter_affineSlab_inter_affineSlab_inter_affineSlab]
  rw [volume_centeredCoordinateWindow _ _ _ hdet]
  rw [Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  ring

end TransverseCoordinateOverlap

end

end Submission.Kakeya.ConvexGeometry
