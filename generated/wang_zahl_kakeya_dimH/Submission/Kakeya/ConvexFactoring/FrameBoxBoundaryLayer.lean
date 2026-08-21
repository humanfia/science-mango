import Submission.Kakeya.ConvexFactoring.BufferedInducedGrowth

/-!
# Frame-box insets and boundary-layer measure

This file computes the volume of the explicit frame-box inset, bounds the
discarded boundary layer by three face contributions, and proves a
division-safe mass-retention lemma for measurable subsets.  The final
statements use only finite nonnegative coefficients and remain valid when the
subset has zero measure or some box side degenerates.  These finite-scale
statements do not assert an endpoint Kakeya estimate.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- The part of a frame box removed by its coordinatewise `r`-inset. -/
def FrameBox.boundaryLayer (B : FrameBox) (r : ℝ≥0) : Set Space :=
  B.carrier \ (B.inset r).carrier

theorem FrameBox.measurableSet_boundaryLayer (B : FrameBox) (r : ℝ≥0) :
    MeasurableSet (B.boundaryLayer r) :=
  B.measurableSet_carrier.diff (B.inset r).measurableSet_carrier

/-- Exact volume of the inset, with truncated subtraction on every side. -/
theorem FrameBox.volume_inset (B : FrameBox) (r : ℝ≥0) :
    volume (B.inset r).carrier =
      ∏ i, ((B.side i - 2 * r : ℝ≥0) : ℝ≥0∞) := by
  rw [(B.inset r).volume_carrier]
  simp only [FrameBox.inset_side]

/-- Frame-box volumes are finite, including for degenerate boxes. -/
theorem FrameBox.volume_carrier_lt_top (B : FrameBox) :
    volume B.carrier < ∞ := by
  rw [B.volume_carrier]
  exact ENNReal.prod_lt_top (fun _ _ ↦ ENNReal.coe_lt_top)

/-- Exact measure of the removed shell. -/
theorem FrameBox.volume_boundaryLayer (B : FrameBox) (r : ℝ≥0) :
    volume (B.boundaryLayer r) =
      (∏ i, (B.side i : ℝ≥0∞)) -
        ∏ i, ((B.side i - 2 * r : ℝ≥0) : ℝ≥0∞) := by
  rw [FrameBox.boundaryLayer,
    measure_sdiff (B.inset_carrier_subset_carrier r)
      (B.inset r).measurableSet_carrier.nullMeasurableSet
      (B.inset r).volume_carrier_lt_top.ne,
    B.volume_carrier, B.volume_inset]

/-- The sum of the three full face-area contributions, multiplied by the
removed full thickness `2r`. -/
def FrameBox.boundaryLayerUpper (B : FrameBox) (r : ℝ≥0) : ℝ≥0 :=
  2 * r *
    (B.side 1 * B.side 2 + B.side 0 * B.side 2 + B.side 0 * B.side 1)

/-- Algebraic three-factor union bound, valid even when `d` exceeds one or
more of the factors because subtraction is truncated. -/
theorem ENNReal.mul_three_sub_tsub_mul_le
    (a b c d : ℝ≥0∞) :
    a * b * c - (a - d) * (b - d) * (c - d) ≤
      d * (b * c + a * c + a * b) := by
  apply (tsub_le_iff_right).2
  have htermA : (a - d) * d * c ≤ d * a * c := by
    calc
      (a - d) * d * c = d * (a - d) * c := by ac_rfl
      _ ≤ d * a * c := by
        gcongr
        exact tsub_le_self
  have htermAB : (a - d) * (b - d) * d ≤ d * a * b := by
    calc
      (a - d) * (b - d) * d = d * (a - d) * (b - d) := by ac_rfl
      _ ≤ d * a * b := by
        gcongr <;> exact tsub_le_self
  calc
    a * b * c ≤ (d + (a - d)) * b * c := by
      gcongr
      exact le_add_tsub
    _ = d * b * c + (a - d) * b * c := by ring
    _ ≤ d * b * c + (a - d) * (d + (b - d)) * c := by
      gcongr
      exact le_add_tsub
    _ = d * b * c + (a - d) * d * c + (a - d) * (b - d) * c := by
      ring
    _ ≤ d * b * c + d * a * c + (a - d) * (b - d) * c := by
      exact add_le_add (add_le_add le_rfl htermA) le_rfl
    _ ≤ d * b * c + d * a * c +
        (a - d) * (b - d) * (d + (c - d)) := by
      gcongr
      exact le_add_tsub
    _ = d * b * c + d * a * c +
        (a - d) * (b - d) * d + (a - d) * (b - d) * (c - d) := by
      ring
    _ ≤ d * b * c + d * a * c + d * a * b +
        (a - d) * (b - d) * (c - d) := by
      exact add_le_add (add_le_add (add_le_add le_rfl le_rfl) htermAB) le_rfl
    _ = d * (b * c + a * c + a * b) +
        (a - d) * (b - d) * (c - d) := by ring

/-- The boundary layer is bounded by the three face-area contributions. -/
theorem FrameBox.volume_boundaryLayer_le_upper (B : FrameBox) (r : ℝ≥0) :
    volume (B.boundaryLayer r) ≤
      (B.boundaryLayerUpper r : ℝ≥0∞) := by
  rw [B.volume_boundaryLayer]
  simp only [Fin.prod_univ_three, ENNReal.coe_sub]
  simpa [FrameBox.boundaryLayerUpper] using
    ENNReal.mul_three_sub_tsub_mul_le
      (B.side 0 : ℝ≥0∞) (B.side 1 : ℝ≥0∞) (B.side 2 : ℝ≥0∞)
      ((2 * r : ℝ≥0) : ℝ≥0∞)

/-- If every side is at least `shortest` and `12r ≤ density * shortest`,
the explicit three-face upper bound is at most half the density fraction of
the box volume. -/
theorem FrameBox.boundaryLayerUpper_le_half_density
    (B : FrameBox) (r density shortest : ℝ≥0)
    (hshort : ∀ i, shortest ≤ B.side i)
    (hscale : 12 * r ≤ density * shortest) :
    B.boundaryLayerUpper r ≤
      density * (∏ i, B.side i) / 2 := by
  rw [FrameBox.boundaryLayerUpper, Fin.prod_univ_three]
  apply NNReal.coe_le_coe.mp
  push_cast
  have hs0 : (shortest : ℝ) ≤ B.side 0 := by exact_mod_cast hshort 0
  have hs1 : (shortest : ℝ) ≤ B.side 1 := by exact_mod_cast hshort 1
  have hs2 : (shortest : ℝ) ≤ B.side 2 := by exact_mod_cast hshort 2
  have hscaleR : 12 * (r : ℝ) ≤ (density : ℝ) * shortest := by
    exact_mod_cast hscale
  have ha : 12 * (r : ℝ) ≤ (density : ℝ) * B.side 0 :=
    hscaleR.trans (mul_le_mul_of_nonneg_left hs0 density.2)
  have hb : 12 * (r : ℝ) ≤ (density : ℝ) * B.side 1 :=
    hscaleR.trans (mul_le_mul_of_nonneg_left hs1 density.2)
  have hc : 12 * (r : ℝ) ≤ (density : ℝ) * B.side 2 :=
    hscaleR.trans (mul_le_mul_of_nonneg_left hs2 density.2)
  have h0 := mul_le_mul_of_nonneg_right ha
    (mul_nonneg (B.side 1).2 (B.side 2).2)
  have h1 := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (B.side 0).2 (B.side 2).2)
  have h2 := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (B.side 0).2 (B.side 1).2)
  calc
    2 * (r : ℝ) *
        (B.side 1 * B.side 2 + B.side 0 * B.side 2 +
          B.side 0 * B.side 1) =
        (12 * (r : ℝ) * (B.side 1 * B.side 2) +
          12 * (r : ℝ) * (B.side 0 * B.side 2) +
          12 * (r : ℝ) * (B.side 0 * B.side 1)) / 6 := by ring
    _ ≤ ((density : ℝ) * B.side 0 * (B.side 1 * B.side 2) +
          (density : ℝ) * B.side 1 * (B.side 0 * B.side 2) +
          (density : ℝ) * B.side 2 * (B.side 0 * B.side 1)) / 6 := by
      exact div_le_div_of_nonneg_right (add_le_add (add_le_add h0 h1) h2)
        (by norm_num)
    _ = (density : ℝ) * (B.side 0 * B.side 1 * B.side 2) / 2 := by ring

/-- The shortest-side condition controls the actual ENNReal measure of the
boundary layer. -/
theorem FrameBox.volume_boundaryLayer_le_half_density
    (B : FrameBox) (r density shortest : ℝ≥0)
    (hshort : ∀ i, shortest ≤ B.side i)
    (hscale : 12 * r ≤ density * shortest) :
    volume (B.boundaryLayer r) ≤
      ((density : ℝ≥0∞) * volume B.carrier) / 2 := by
  calc
    volume (B.boundaryLayer r) ≤ (B.boundaryLayerUpper r : ℝ≥0∞) :=
      B.volume_boundaryLayer_le_upper r
    _ ≤ ((density * (∏ i, B.side i) / 2 : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr
        (B.boundaryLayerUpper_le_half_density r density shortest hshort hscale)
    _ = ((density : ℝ≥0∞) * volume B.carrier) / 2 := by
      rw [B.volume_carrier]
      push_cast
      rfl

/-- If the discarded shell has at most half the density-guaranteed ambient
mass, then at least half of `A` remains in the inset.  The proof performs no
division by `volume A` or by the box volume. -/
theorem FrameBox.half_mass_le_inter_inset
    (B : FrameBox) (r density : ℝ≥0) {A : Set Space}
    (_hAmeas : MeasurableSet A) (hA : A ⊆ B.carrier)
    (hlower : (density : ℝ≥0∞) * volume B.carrier ≤ volume A)
    (hshell : volume (B.boundaryLayer r) ≤
      ((density : ℝ≥0∞) * volume B.carrier) / 2) :
    volume A / 2 ≤ volume (A ∩ (B.inset r).carrier) := by
  have houtside : A \ (B.inset r).carrier ⊆ B.boundaryLayer r := by
    intro x hx
    exact ⟨hA hx.1, hx.2⟩
  have houtside_le :
      volume (A \ (B.inset r).carrier) ≤ volume A / 2 :=
    (measure_mono houtside).trans <| hshell.trans <|
      ENNReal.div_le_div_right hlower 2
  have hdecomp :
      volume (A ∩ (B.inset r).carrier) +
        volume (A \ (B.inset r).carrier) = volume A :=
    measure_inter_add_sdiff A (B.inset r).measurableSet_carrier
  have hhalf_ne : volume A / 2 ≠ ∞ := by
    have hAfin : volume A < ∞ :=
      (measure_mono hA).trans_lt B.volume_carrier_lt_top
    exact (ENNReal.div_lt_top hAfin.ne (by norm_num)).ne
  apply (ENNReal.add_le_add_iff_right hhalf_ne).mp
  rw [ENNReal.add_halves]
  calc
    volume A = volume (A ∩ (B.inset r).carrier) +
        volume (A \ (B.inset r).carrier) := hdecomp.symm
    _ ≤ volume (A ∩ (B.inset r).carrier) + volume A / 2 :=
      add_le_add le_rfl houtside_le

/-- Division-free form of half-mass retention. -/
theorem FrameBox.volume_le_two_mul_inter_inset
    (B : FrameBox) (r density : ℝ≥0) {A : Set Space}
    (hAmeas : MeasurableSet A) (hA : A ⊆ B.carrier)
    (hlower : (density : ℝ≥0∞) * volume B.carrier ≤ volume A)
    (hshell : volume (B.boundaryLayer r) ≤
      ((density : ℝ≥0∞) * volume B.carrier) / 2) :
    volume A ≤ 2 * volume (A ∩ (B.inset r).carrier) := by
  have hhalf := B.half_mass_le_inter_inset r density hAmeas hA hlower hshell
  calc
    volume A = volume A / 2 + volume A / 2 := ENNReal.add_halves _ |>.symm
    _ ≤ volume (A ∩ (B.inset r).carrier) +
        volume (A ∩ (B.inset r).carrier) := add_le_add hhalf hhalf
    _ = 2 * volume (A ∩ (B.inset r).carrier) := by ring

/-- Choosing the inset radius to be one twelfth of
`density * shortest` makes the shell small enough automatically. -/
theorem FrameBox.volume_boundaryLayer_le_half_density_at_shortest_scale
    (B : FrameBox) (density shortest : ℝ≥0)
    (hshort : ∀ i, shortest ≤ B.side i) :
    volume (B.boundaryLayer (density * shortest / 12)) ≤
      ((density : ℝ≥0∞) * volume B.carrier) / 2 := by
  apply B.volume_boundaryLayer_le_half_density
    (density * shortest / 12) density shortest hshort
  apply le_of_eq
  apply NNReal.eq
  push_cast
  ring

/-- Fully explicit, division-free mass retention at the shortest-side scale.
It is valid without nonzero assumptions on the density, shortest side, or
ambient box volume. -/
theorem FrameBox.volume_le_two_mul_inter_inset_at_shortest_scale
    (B : FrameBox) (density shortest : ℝ≥0) {A : Set Space}
    (hAmeas : MeasurableSet A) (hA : A ⊆ B.carrier)
    (hshort : ∀ i, shortest ≤ B.side i)
    (hlower : (density : ℝ≥0∞) * volume B.carrier ≤ volume A) :
    volume A ≤
      2 * volume
        (A ∩ (B.inset (density * shortest / 12)).carrier) := by
  exact B.volume_le_two_mul_inter_inset
    (density * shortest / 12) density hAmeas hA hlower
    (B.volume_boundaryLayer_le_half_density_at_shortest_scale
      density shortest hshort)

end

end Submission.Kakeya.ConvexGeometry
