import Mathlib.MeasureTheory.Measure.Real

/-!
# Transfer from centered concentration to a deterministic limit

This module records the elementary event inclusion used to combine a
finite-volume concentration inequality around an expectation with
convergence of those expectations to a deterministic thermodynamic limit.
-/

namespace ArchonPhysics.CenteredConcentrationTransfer

open MeasureTheory Set

variable {Omega : Type*} [MeasurableSpace Omega]

omit [MeasurableSpace Omega] in
/-- If the deterministic center is within `delta` of `L`, an `epsilon`
deviation from `L` forces an `epsilon - delta` deviation from the center. -/
theorem deviation_set_subset_centered
    (X : Omega → Real) (a L epsilon delta : Real)
    (ha : |a - L| ≤ delta) :
    {omega | epsilon < |X omega - L|} ⊆
      {omega | epsilon - delta < |X omega - a|} := by
  intro omega homega
  change epsilon < |X omega - L| at homega
  have htriangle :
      |X omega - L| ≤ |X omega - a| + |a - L| := by
    calc
      |X omega - L| = |(X omega - a) + (a - L)| := by ring_nf
      _ ≤ |X omega - a| + |a - L| := abs_add_le _ _
  change epsilon - delta < |X omega - a|
  linarith

/-- Measure version of `deviation_set_subset_centered`.  No measurability
hypothesis is needed for monotonicity of an outer measure. -/
theorem measure_deviation_le_centered
    (mu : Measure Omega) (X : Omega → Real)
    (a L epsilon delta : Real) (ha : |a - L| ≤ delta) :
    mu {omega | epsilon < |X omega - L|} ≤
      mu {omega | epsilon - delta < |X omega - a|} :=
  measure_mono (deviation_set_subset_centered X a L epsilon delta ha)

/-- A quantitative centered tail bound transfers unchanged to a tail bound
around the deterministic limit once the center error is accounted for. -/
theorem measure_deviation_le_of_centered_bound
    (mu : Measure Omega) (X : Omega → Real)
    (a L epsilon delta : Real) (b : ENNReal)
    (ha : |a - L| ≤ delta)
    (hcentered :
      mu {omega | epsilon - delta < |X omega - a|} ≤ b) :
    mu {omega | epsilon < |X omega - L|} ≤ b :=
  (measure_deviation_le_centered mu X a L epsilon delta ha).trans hcentered

/-- Convenient half-error specialization. -/
theorem measure_deviation_le_half_centered
    (mu : Measure Omega) (X : Omega → Real)
    (a L epsilon : Real) (b : ENNReal)
    (ha : |a - L| ≤ epsilon / 2)
    (hcentered : mu {omega | epsilon / 2 < |X omega - a|} ≤ b) :
    mu {omega | epsilon < |X omega - L|} ≤ b := by
  apply measure_deviation_le_of_centered_bound
    mu X a L epsilon (epsilon / 2) b ha
  have hhalf : epsilon - epsilon / 2 = epsilon / 2 := by ring
  rw [hhalf]
  exact hcentered

end ArchonPhysics.CenteredConcentrationTransfer
