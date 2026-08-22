import ChallengeDeps

open scoped NNReal Pointwise

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Certified dimensions for three-dimensional convex bodies

The Wang--Zahl argument describes the dimensions of a convex body using the
axes of its outer John ellipsoid.  The existence and extremality theory for
that ellipsoid is deliberately not assumed here.  Instead, `HasBoxDimensions`
records the concrete inner/outer comparison certificate used by later
estimates.  A future John-ellipsoid layer can construct this certificate.
-/

/-- An oriented, centered box in three-dimensional Euclidean space.

The entries of `side` are full side lengths in the orthonormal frame. -/
structure FrameBox where
  center : Space
  frame : OrthonormalBasis (Fin 3) ℝ Space
  side : Fin 3 → ℝ≥0


/-- The edge vector of an oriented box in one frame direction. -/
def FrameBox.edge (B : FrameBox) (i : Fin 3) : Space :=
  (B.side i : ℝ) • B.frame i

/-- The corner from which Mathlib's `[0,1]³` parallelepiped is translated. -/
def FrameBox.corner (B : FrameBox) : Space :=
  B.center - ∑ i, (2 : ℝ)⁻¹ • B.edge i

/-- The closed carrier of an oriented, centered box. -/
def FrameBox.carrier (B : FrameBox) : Set Space :=
  (fun x ↦ B.corner + x) '' parallelepiped B.edge

/-- The carrier of a frame box is convex. -/
theorem FrameBox.convex_carrier (B : FrameBox) : Convex ℝ B.carrier := by
  exact (convex_parallelepiped B.edge).translate B.corner

/-- The carrier of a frame box is compact, including when some side is zero. -/
theorem FrameBox.isCompact_carrier (B : FrameBox) : IsCompact B.carrier := by
  apply IsCompact.image
  · exact isCompact_Icc.image <|
      continuous_finsetSum Finset.univ fun i _ ↦
        continuous_apply i |>.smul continuous_const
  · fun_prop

/-- The declared center belongs to the box. -/
theorem FrameBox.center_mem_carrier (B : FrameBox) : B.center ∈ B.carrier := by
  let t : Fin 3 → ℝ := fun _ ↦ (2 : ℝ)⁻¹
  refine ⟨∑ i, t i • B.edge i, ?_, ?_⟩
  · rw [mem_parallelepiped_iff]
    refine ⟨t, ?_, rfl⟩
    constructor <;> intro i <;> norm_num [t]
  · simp only [corner, t]
    abel

/-- A frame box regarded as a Mathlib convex body. -/
def FrameBox.body (B : FrameBox) : ConvexBody Space where
  carrier := B.carrier
  convex' := B.convex_carrier
  isCompact' := B.isCompact_carrier
  nonempty' := ⟨B.center, B.center_mem_carrier⟩

@[simp]
theorem FrameBox.coe_body (B : FrameBox) : (B.body : Set Space) = B.carrier :=
  rfl

/-- Rescale every side length while keeping the same center and frame. -/
def FrameBox.rescale (r : ℝ≥0) (B : FrameBox) : FrameBox where
  center := B.center
  frame := B.frame
  side := fun i ↦ r * B.side i

@[simp]
theorem FrameBox.rescale_center (r : ℝ≥0) (B : FrameBox) :
    (B.rescale r).center = B.center :=
  rfl

@[simp]
theorem FrameBox.rescale_frame (r : ℝ≥0) (B : FrameBox) :
    (B.rescale r).frame = B.frame :=
  rfl

@[simp]
theorem FrameBox.rescale_side (r : ℝ≥0) (B : FrameBox) (i : Fin 3) :
    (B.rescale r).side i = r * B.side i :=
  rfl


/-- The side-length pattern `θ × 1 × 1`. -/
def slabSides (θ : ℝ≥0) : Fin 3 → ℝ≥0 :=
  ![θ, 1, 1]

/-- The side-length pattern `a × b × 1`. -/
def plankSides (a b : ℝ≥0) : Fin 3 → ℝ≥0 :=
  ![a, b, 1]

/-- A checked `C`-comparability certificate for the dimensions of a convex
body.  The body lies in the displayed box and contains its concentric
`C⁻¹` rescaling. -/
def HasBoxDimensions (C : ℝ≥0) (side : Fin 3 → ℝ≥0)
    (K : ConvexBody Space) : Prop :=
  1 ≤ C ∧ ∃ box : FrameBox,
    box.side = side ∧
      (box.rescale C⁻¹).body ≤ K ∧
      K ≤ box.body

/-- A certified slab has dimensions comparable to `θ × 1 × 1`. -/
def IsSlab (C θ : ℝ≥0) (K : ConvexBody Space) : Prop :=
  0 < θ ∧ θ ≤ 1 ∧ HasBoxDimensions C (slabSides θ) K

/-- A certified plank has dimensions comparable to `a × b × 1`. -/
def IsPlank (C a b : ℝ≥0) (K : ConvexBody Space) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ 1 ∧ HasBoxDimensions C (plankSides a b) K

end

end Submission.Kakeya.ConvexGeometry
