import FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1

open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

/-!
# Positivity and finiteness of the single-dyadic selection loss

The admitted label interval is nonempty whenever the lower scale is positive
and no larger than the ceiling.  Hence its exact cardinality is a positive
finite ENNReal denominator, as required by the selection telescope.
-/

theorem continuumCriticalSingleDyadicBinFactor_pos
    {delta ceiling : Real} (hdelta : 0 < delta)
    (hdeltaCeiling : delta ≤ ceiling) :
    0 < continuumCriticalSingleDyadicBinFactor delta ceiling := by
  have hbucket : dyadicCeilBucket delta ≤ dyadicCeilBucket ceiling :=
    dyadicCeilBucket_mono hdelta hdeltaCeiling
  unfold continuumCriticalSingleDyadicBinFactor
  have hpos : (0 : Int) <
      dyadicCeilBucket ceiling + 1 - dyadicCeilBucket delta := by
    omega
  rw [← Int.ofNat_lt, Int.toNat_of_nonneg hpos.le]
  exact hpos

theorem continuumCriticalSingleDyadicBinFactor_cast_ne_zero
    {delta ceiling : Real} (hdelta : 0 < delta)
    (hdeltaCeiling : delta ≤ ceiling) :
    (continuumCriticalSingleDyadicBinFactor delta ceiling : ENNReal) ≠ 0 := by
  exact_mod_cast
    (continuumCriticalSingleDyadicBinFactor_pos hdelta hdeltaCeiling).ne'

theorem continuumCriticalSingleDyadicBinFactor_cast_ne_top
    (delta ceiling : Real) :
    (continuumCriticalSingleDyadicBinFactor delta ceiling : ENNReal) ≠ ⊤ :=
  ENNReal.natCast_ne_top _

#print axioms continuumCriticalSingleDyadicBinFactor_pos
#print axioms continuumCriticalSingleDyadicBinFactor_cast_ne_zero
#print axioms continuumCriticalSingleDyadicBinFactor_cast_ne_top

end FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
