import ArchonPhysics.ChildRepeatedReducedResonanceLineNullity

/-!
# Planar volume of the child-repeated resonance strip

Inside a bounded physical frequency square, the strip
`|omega_parent - 2 * omega_child| <= delta` has area at most
`2 * W * delta`.  This converts a two-frequency density estimate into the
linear small-ball estimate required by the child-repeated weak-limit closure.
-/

namespace ArchonPhysics.ChildRepeatedReducedResonanceStripVolume

open ArchonPhysics
open ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Closed reduced resonance strip of half-width `delta`. -/
def childRepeatedReducedResonanceStrip (delta : Real) : Set (Real × Real) :=
  {frequency | |childRepeatedDecayMismatch frequency| ≤ delta}

/-- The physical parent/child frequency square. -/
def childRepeatedFrequencySquare (W : Real) : Set (Real × Real) :=
  Icc 0 W ×ˢ Icc 0 W

theorem childRepeatedReducedResonanceStrip_isClosed (delta : Real) :
    IsClosed (childRepeatedReducedResonanceStrip delta) := by
  exact isClosed_le
    (continuous_abs.comp continuous_childRepeatedDecayMismatch)
    continuous_const

theorem childRepeatedFrequencySquare_isClosed (W : Real) :
    IsClosed (childRepeatedFrequencySquare W) :=
  (isClosed_Icc.prod isClosed_Icc)

/-- On a fixed child-frequency slice, membership in the resonance strip
forces the parent into an interval of length `2 * delta`. -/
theorem parent_mem_resonanceInterval_of_mem_strip
    {parent child delta : Real}
    (hfrequency :
      (parent, child) ∈ childRepeatedReducedResonanceStrip delta) :
    parent ∈ Icc (2 * child - delta) (2 * child + delta) := by
  change |parent - 2 * child| ≤ delta at hfrequency
  rw [abs_le] at hfrequency
  constructor <;> linarith

/-- Explicit `O(delta)` planar-volume bound on the bounded physical square. -/
theorem volume_childRepeatedReducedResonanceStrip_inter_frequencySquare_le
    {W delta : Real} (_hW : 0 ≤ W) (hdelta : 0 ≤ delta) :
    (volume : Measure (Real × Real))
        (childRepeatedReducedResonanceStrip delta ∩
          childRepeatedFrequencySquare W) ≤
      ENNReal.ofReal (2 * W * delta) := by
  let target := childRepeatedReducedResonanceStrip delta ∩
    childRepeatedFrequencySquare W
  have htarget : MeasurableSet target :=
    (childRepeatedReducedResonanceStrip_isClosed delta).measurableSet.inter
      (childRepeatedFrequencySquare_isClosed W).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm htarget]
  calc
    (∫⁻ child, (volume : Measure Real)
        ((fun parent => (parent, child)) ⁻¹' target) ∂volume) ≤
      ∫⁻ child in Icc (0 : Real) W,
        ENNReal.ofReal (2 * delta) ∂volume := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_mono_ae
      filter_upwards with child
      by_cases hchild : child ∈ Icc (0 : Real) W
      · rw [indicator_of_mem hchild]
        calc
          (volume : Measure Real)
              ((fun parent => (parent, child)) ⁻¹' target) ≤
            (volume : Measure Real)
              (Icc (2 * child - delta) (2 * child + delta)) := by
                apply measure_mono
                intro parent hparent
                exact parent_mem_resonanceInterval_of_mem_strip hparent.1
          _ = ENNReal.ofReal (2 * delta) := by
            rw [Real.volume_Icc]
            congr 1
            ring
      · rw [indicator_of_notMem hchild]
        have hsection :
            ((fun parent => (parent, child)) ⁻¹' target) = ∅ := by
          ext parent
          simp only [mem_preimage, mem_empty_iff_false]
          constructor
          · intro hparent
            exact (hchild hparent.2.2)
          · intro hfalse
            exact False.elim hfalse
        rw [hsection, measure_empty]
    _ = ENNReal.ofReal (2 * delta) *
        (volume : Measure Real) (Icc (0 : Real) W) := by
      rw [setLIntegral_const]
    _ = ENNReal.ofReal (2 * W * delta) := by
      rw [Real.volume_Icc]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * delta)]
      congr 1
      ring

end


end ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
