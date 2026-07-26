import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0068

open Dimension

/-!
# Images of a red ball in two perpendicular plane mirrors

The coordinate origin is the common end of two `3 m` plane-mirror segments.
The horizontal mirror occupies the negative `x`-axis and the vertical mirror
occupies the negative `y`-axis.  Thus the primary figure places the red ball
at `A = (-1,-2) m`; its caption's claim that `A` is right of the vertical
mirror conflicts with the image and is not used.

Coordinates below are explicitly scalar readouts in SI metres, as permitted
for a measured coordinate diagram.  Mirror lengths themselves use Physlib's
unit-independent dimensionful quantities.  Each mirror retains both its
infinite carrier (needed for the method of images) and its finite reflecting
segment (shown in the figure).
-/

/-- Positions in the two-dimensional optical diagram, read in SI metres. -/
abbrev OpticalPlane := EuclideanSpace ℝ (Fin 2)

/-- A physical length represented coherently in every choice of units. -/
abbrev LengthQuantity := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a physical length when the SI metre is selected. -/
def lengthInMetres (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Labels of the two blue plane-mirror segments in the primary figure. -/
inductive MirrorLabel where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The color information attached to the object at `A`. -/
inductive BallColor where
  | red
  | other
  deriving DecidableEq, Repr

/--
A finite plane mirror: `carrier` is the complete affine line used by the
method of images, while `reflectingSegment` is the physical, finite mirror.
`length` is a unit-independent physical length.
-/
structure FinitePlaneMirror where
  carrier : AffineSubspace ℝ OpticalPlane
  reflectingSegment : Set OpticalPlane
  length : LengthQuantity
  carrierNonempty : Nonempty carrier
  reflectingSegment_on_carrier :
    reflectingSegment ⊆ (carrier : Set OpticalPlane)

/-- Reflection of a point in the complete carrier line of a plane mirror. -/
noncomputable def reflectInMirror
    (mirror : FinitePlaneMirror) (point : OpticalPlane) : OpticalPlane :=
  letI : Nonempty mirror.carrier := mirror.carrierNonempty
  EuclideanGeometry.reflection mirror.carrier point

/--
The physical scene: the corner and labels from the figure, the red ball at
`A`, the observer at `O`, and the physical relation saying that `O` sees a
virtual image at a specified apparent position.
-/
structure PerpendicularMirrorScene where
  mirror : MirrorLabel → FinitePlaneMirror
  corner : OpticalPlane
  ballPosition : OpticalPlane
  ballColor : BallColor
  observerPosition : OpticalPlane
  observerSeesVirtualImageAt : OpticalPlane → Prop

/-- Apply a list of mirror reflections to the ball's position, in list order. -/
noncomputable def applyReflectionSequence
    (scene : PerpendicularMirrorScene)
    (sequence : List MirrorLabel) : OpticalPlane :=
  sequence.foldl
    (fun point label => reflectInMirror (scene.mirror label) point)
    scene.ballPosition

/--
A single-reflection image is visible when the ray from `O` toward its apparent
position meets the physical reflecting segment at an interior ray parameter.
The straight line to the reflected point is the unfolded form of the usual
equal-angle specular path.
-/
def IsVisibleSingleReflectionImage
    (scene : PerpendicularMirrorScene)
    (label : MirrorLabel) (apparentPoint : OpticalPlane) : Prop :=
  applyReflectionSequence scene [label] = apparentPoint ∧
    ∃ t : ℝ,
      t ∈ Set.Ioo 0 1 ∧
        AffineMap.lineMap scene.observerPosition apparentPoint t ∈
          (scene.mirror label).reflectingSegment

/--
A two-reflection image is visible when the unfolded observer ray first meets
one physical mirror segment and then the other segment after the first mirror
has reflected it.  Ordering the two open-segment parameters retains which
mirror is encountered first.  This is the method-of-images construction for a
finite two-mirror ray path; it asserts no image count.
-/
def IsVisibleDoubleReflectionImage
    (scene : PerpendicularMirrorScene)
    (first second : MirrorLabel) (apparentPoint : OpticalPlane) : Prop :=
  first ≠ second ∧
    applyReflectionSequence scene [second, first] = apparentPoint ∧
      ∃ tFirst tSecond : ℝ,
        tFirst ∈ Set.Ioo 0 1 ∧
          tSecond ∈ Set.Ioo 0 1 ∧
          tFirst < tSecond ∧
          AffineMap.lineMap scene.observerPosition apparentPoint tFirst ∈
            (scene.mirror first).reflectingSegment ∧
          AffineMap.lineMap scene.observerPosition apparentPoint tSecond ∈
            reflectInMirror (scene.mirror first) ''
              (scene.mirror second).reflectingSegment

/--
An apparent point with a finite specular route through one or both mirrors.
For the pictured perpendicular pair, these are precisely the possible
non-original virtual-image positions, but that fact remains to be proved.
-/
def IsVisibleReflectionImagePosition
    (scene : PerpendicularMirrorScene) (point : OpticalPlane) : Prop :=
  (∃ label, IsVisibleSingleReflectionImage scene label point) ∨
    ∃ first second,
      IsVisibleDoubleReflectionImage scene first second point

/-- The set of distinct apparent image positions seen by the observer at `O`. -/
def seenVirtualImagePositions
    (scene : PerpendicularMirrorScene) : Set OpticalPlane :=
  {point | scene.observerSeesVirtualImageAt point}

/--
Primary-image readouts and spatial relations.  The two mirror segments each
have length `3 m`; their common endpoint is the coordinate origin; and the
red ball is `1 m` left of the vertical mirror and `2 m` below the horizontal
mirror.  The unlabelled point `O` is aligned below the left end of the
horizontal mirror and lies vertically between `A` and the lower mirror end.

No image position or image count is asserted here.
-/
structure MatchesPerpendicularMirrorFigure
    (scene : PerpendicularMirrorScene) : Prop where
  corner_at_origin : scene.corner = !₂[(0 : ℝ), 0]
  horizontal_carrier :
    ∀ point : OpticalPlane,
      point ∈ (scene.mirror .horizontal).carrier ↔ point 1 = 0
  vertical_carrier :
    ∀ point : OpticalPlane,
      point ∈ (scene.mirror .vertical).carrier ↔ point 0 = 0
  horizontal_segment :
    ∀ point : OpticalPlane,
      point ∈ (scene.mirror .horizontal).reflectingSegment ↔
        point 1 = 0 ∧ point 0 ∈ Set.Icc (-3 : ℝ) 0
  vertical_segment :
    ∀ point : OpticalPlane,
      point ∈ (scene.mirror .vertical).reflectingSegment ↔
        point 0 = 0 ∧ point 1 ∈ Set.Icc (-3 : ℝ) 0
  horizontal_length_readout :
    lengthInMetres (scene.mirror .horizontal).length = 3
  vertical_length_readout :
    lengthInMetres (scene.mirror .vertical).length = 3
  ball_is_red : scene.ballColor = .red
  point_A_readout : scene.ballPosition = !₂[(-1 : ℝ), -2]
  point_O_horizontal_alignment : scene.observerPosition 0 = -3
  point_O_above_vertical_mirror_end : -3 < scene.observerPosition 1
  point_O_below_A : scene.observerPosition 1 < -2

/--
The geometrical-optics method-of-images law for this finite two-mirror view:
an apparent point is seen exactly when it admits one of the unfolded specular
routes above.  This is a local physics interface because Mathlib supplies
affine reflection and Physlib supplies physical units, but neither library
supplies observer-visible virtual images for finite plane mirrors.  The law
does not state or enumerate any image positions or image count.
-/
structure ObeysPlaneMirrorImageLaw
    (scene : PerpendicularMirrorScene) : Prop where
  image_seen_iff_visible_specular_route :
    ∀ point : OpticalPlane,
      scene.observerSeesVirtualImageAt point ↔
        IsVisibleReflectionImagePosition scene point

/--
For the finite perpendicular mirrors, displayed positions of `A` and `O`, and
the unfolded finite-segment tests, the visible specular routes end at the
three usual single- and double-reflection positions.
-/
lemma visibleReflectionImagePositions_from_figure
    (scene : PerpendicularMirrorScene)
    (hFigure : MatchesPerpendicularMirrorFigure scene) :
    {point | IsVisibleReflectionImagePosition scene point} =
      ({!₂[(-1 : ℝ), 2], !₂[(1 : ℝ), -2], !₂[(1 : ℝ), 2]} :
        Set OpticalPlane) := by
  have horizontal_reflection (point : OpticalPlane) :
      reflectInMirror (scene.mirror .horizontal) point =
        !₂[point 0, -point 1] := by
    letI : Nonempty (scene.mirror .horizontal).carrier :=
      (scene.mirror .horizontal).carrierNonempty
    let base : OpticalPlane := !₂[point 0, 0]
    let normal : OpticalPlane := !₂[0, point 1]
    have hbase : base ∈ (scene.mirror .horizontal).carrier := by
      rw [hFigure.horizontal_carrier]
      simp [base]
    have hnormal :
        normal ∈ (scene.mirror .horizontal).carrier.directionᗮ := by
      rw [Submodule.mem_orthogonal]
      intro direction hdirection
      have htranslated :
          direction +ᵥ base ∈ (scene.mirror .horizontal).carrier :=
        (scene.mirror .horizontal).carrier.vadd_mem_of_mem_direction
          hdirection hbase
      have hcoordinate :
          direction 1 = 0 := by
        have := (hFigure.horizontal_carrier (direction +ᵥ base)).mp htranslated
        simpa [base] using this
      simp [normal, PiLp.inner_apply, Fin.sum_univ_two, hcoordinate]
    have hpoint : point = normal +ᵥ base := by
      ext i
      fin_cases i <;> simp [normal, base]
    rw [hpoint]
    unfold reflectInMirror
    rw [EuclideanGeometry.reflection_orthogonal_vadd hbase hnormal]
    ext i
    fin_cases i <;> simp [normal, base]
  have vertical_reflection (point : OpticalPlane) :
      reflectInMirror (scene.mirror .vertical) point =
        !₂[-point 0, point 1] := by
    letI : Nonempty (scene.mirror .vertical).carrier :=
      (scene.mirror .vertical).carrierNonempty
    let base : OpticalPlane := !₂[0, point 1]
    let normal : OpticalPlane := !₂[point 0, 0]
    have hbase : base ∈ (scene.mirror .vertical).carrier := by
      rw [hFigure.vertical_carrier]
      simp [base]
    have hnormal :
        normal ∈ (scene.mirror .vertical).carrier.directionᗮ := by
      rw [Submodule.mem_orthogonal]
      intro direction hdirection
      have htranslated :
          direction +ᵥ base ∈ (scene.mirror .vertical).carrier :=
        (scene.mirror .vertical).carrier.vadd_mem_of_mem_direction
          hdirection hbase
      have hcoordinate :
          direction 0 = 0 := by
        have := (hFigure.vertical_carrier (direction +ᵥ base)).mp htranslated
        simpa [base] using this
      simp [normal, PiLp.inner_apply, Fin.sum_univ_two, hcoordinate]
    have hpoint : point = normal +ᵥ base := by
      ext i
      fin_cases i <;> simp [normal, base]
    rw [hpoint]
    unfold reflectInMirror
    rw [EuclideanGeometry.reflection_orthogonal_vadd hbase hnormal]
    ext i
    fin_cases i <;> simp [normal, base]
  have lineMap_coordinate
      (start finish : OpticalPlane) (t : ℝ) (i : Fin 2) :
      (AffineMap.lineMap start finish t) i =
        (1 - t) * start i + t * finish i := by
    simp [AffineMap.lineMap_apply_module]
  ext point
  constructor
  · intro hpoint
    change IsVisibleReflectionImagePosition scene point at hpoint
    rcases hpoint with hsingle | hdouble
    · rcases hsingle with ⟨label, himage, _⟩
      cases label with
      | horizontal =>
          have himage' : !₂[(-1 : ℝ), 2] = point := by
            simpa [applyReflectionSequence, hFigure.point_A_readout,
              horizontal_reflection] using himage
          simp [← himage']
      | vertical =>
          have himage' : !₂[(1 : ℝ), -2] = point := by
            simpa [applyReflectionSequence, hFigure.point_A_readout,
              vertical_reflection] using himage
          simp [← himage']
    · rcases hdouble with ⟨first, second, hne, himage, _⟩
      cases first <;> cases second
      · exact (hne rfl).elim
      · have himage' : !₂[(1 : ℝ), 2] = point := by
          simpa [applyReflectionSequence, hFigure.point_A_readout,
            horizontal_reflection, vertical_reflection] using himage
        simp [← himage']
      · have himage' : !₂[(1 : ℝ), 2] = point := by
          simpa [applyReflectionSequence, hFigure.point_A_readout,
            horizontal_reflection, vertical_reflection] using himage
        simp [← himage']
      · exact (hne rfl).elim
  · intro hpoint
    change point = !₂[(-1 : ℝ), 2] ∨
      point = !₂[(1 : ℝ), -2] ∨ point = !₂[(1 : ℝ), 2] at hpoint
    rcases hpoint with rfl | rfl | rfl
    · left
      refine ⟨.horizontal, ?_, ?_⟩
      · simpa [applyReflectionSequence, hFigure.point_A_readout] using
          horizontal_reflection !₂[(-1 : ℝ), -2]
      · let observerY : ℝ := scene.observerPosition 1
        let tHorizontal : ℝ := -observerY / (2 - observerY)
        have hyLower : -3 < observerY := by
          simpa [observerY] using hFigure.point_O_above_vertical_mirror_end
        have hyUpper : observerY < -2 := by
          simpa [observerY] using hFigure.point_O_below_A
        have hdenominator : 0 < 2 - observerY := by linarith
        have htPositive : 0 < tHorizontal := by
          exact div_pos (by linarith) hdenominator
        have htBelowOne : tHorizontal < 1 := by
          apply (div_lt_one hdenominator).2
          linarith
        refine ⟨tHorizontal, ⟨htPositive, htBelowOne⟩, ?_⟩
        rw [hFigure.horizontal_segment]
        constructor
        · rw [lineMap_coordinate]
          change
            (1 - tHorizontal) * observerY + tHorizontal * 2 = 0
          dsimp [tHorizontal]
          field_simp [ne_of_gt hdenominator]
          ring
        · rw [Set.mem_Icc]
          rw [lineMap_coordinate]
          have hx :
              scene.observerPosition 0 = -3 :=
            hFigure.point_O_horizontal_alignment
          norm_num [hx]
          constructor <;> nlinarith
    · left
      refine ⟨.vertical, ?_, ?_⟩
      · simpa [applyReflectionSequence, hFigure.point_A_readout] using
          vertical_reflection !₂[(-1 : ℝ), -2]
      · refine ⟨(3 / 4 : ℝ), by norm_num, ?_⟩
        rw [hFigure.vertical_segment]
        constructor
        · rw [lineMap_coordinate]
          rw [hFigure.point_O_horizontal_alignment]
          norm_num
        · rw [Set.mem_Icc]
          rw [lineMap_coordinate]
          have hyLower :
              -3 < scene.observerPosition 1 :=
            hFigure.point_O_above_vertical_mirror_end
          have hyUpper :
              scene.observerPosition 1 < -2 :=
            hFigure.point_O_below_A
          constructor <;> norm_num <;> linarith
    · right
      refine ⟨.horizontal, .vertical, by decide, ?_, ?_⟩
      · simp [applyReflectionSequence, hFigure.point_A_readout,
          vertical_reflection, horizontal_reflection]
      · let observerY : ℝ := scene.observerPosition 1
        let tHorizontal : ℝ := -observerY / (2 - observerY)
        have hyLower : -3 < observerY := by
          simpa [observerY] using hFigure.point_O_above_vertical_mirror_end
        have hyUpper : observerY < -2 := by
          simpa [observerY] using hFigure.point_O_below_A
        have hdenominator : 0 < 2 - observerY := by linarith
        have htPositive : 0 < tHorizontal := by
          exact div_pos (by linarith) hdenominator
        have htBelowOne : tHorizontal < 1 := by
          apply (div_lt_one hdenominator).2
          linarith
        have htBeforeVertical : tHorizontal < (3 / 4 : ℝ) := by
          apply (div_lt_iff₀ hdenominator).2
          nlinarith
        refine ⟨tHorizontal, (3 / 4 : ℝ),
          ⟨htPositive, htBelowOne⟩, by norm_num, htBeforeVertical, ?_, ?_⟩
        · rw [hFigure.horizontal_segment]
          constructor
          · rw [lineMap_coordinate]
            change
              (1 - tHorizontal) * observerY + tHorizontal * 2 = 0
            dsimp [tHorizontal]
            field_simp [ne_of_gt hdenominator]
            ring
          · rw [Set.mem_Icc]
            rw [lineMap_coordinate]
            rw [hFigure.point_O_horizontal_alignment]
            constructor <;> norm_num <;> nlinarith
        · let reflectedHit : OpticalPlane :=
            !₂[(0 : ℝ), -(observerY / 4 + 3 / 2)]
          refine ⟨reflectedHit, ?_, ?_⟩
          · rw [hFigure.vertical_segment]
            constructor
            · simp [reflectedHit]
            · rw [Set.mem_Icc]
              norm_num [reflectedHit]
              constructor <;> nlinarith
          · rw [horizontal_reflection]
            ext i
            fin_cases i <;>
              simp [reflectedHit, lineMap_coordinate,
                hFigure.point_O_horizontal_alignment, observerY] <;>
              ring

/--
The method-of-images law transfers the geometrically computed reflection
orbit to the distinct virtual-image positions visible from `O`.
-/
lemma seenVirtualImagePositions_from_figure
    (scene : PerpendicularMirrorScene)
    (hFigure : MatchesPerpendicularMirrorFigure scene)
    (hOptics : ObeysPlaneMirrorImageLaw scene) :
    seenVirtualImagePositions scene =
      ({!₂[(-1 : ℝ), 2], !₂[(1 : ℝ), -2], !₂[(1 : ℝ), 2]} :
        Set OpticalPlane) := by
  calc
    seenVirtualImagePositions scene =
        {point | IsVisibleReflectionImagePosition scene point} := by
      ext point
      exact hOptics.image_seen_iff_visible_specular_route point
    _ = ({!₂[(-1 : ℝ), 2], !₂[(1 : ℝ), -2], !₂[(1 : ℝ), 2]} :
        Set OpticalPlane) :=
      visibleReflectionImagePositions_from_figure scene hFigure

/-- Labels of the four answer choices displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Image count printed beside each answer label. -/
def AnswerChoice.imageCount : AnswerChoice → ℕ
  | .A => 4
  | .B => 5
  | .C => 3
  | .D => 1

/-- Dataset metadata: the recorded answer label, not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/--
An observer at the depicted point `O` sees exactly three distinct virtual
images of the red ball at `A`, so the recorded answer is choice C.

Blueprint label: `thm:physics:phyx_mini_0068:target`.
-/
theorem observer_at_O_sees_three_images
    (scene : PerpendicularMirrorScene)
    (hFigure : MatchesPerpendicularMirrorFigure scene)
    (hOptics : ObeysPlaneMirrorImageLaw scene) :
    (seenVirtualImagePositions scene).ncard = 3 := by
  rw [seenVirtualImagePositions_from_figure scene hFigure hOptics]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0068
