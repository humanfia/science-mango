import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8SelectedParentPlankCenteredAdaptiveScaleFlatnessAuditV4

open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1

noncomputable section

/-!
# Audit of the missing occupied-bucket flatness input

The weighted three-side pigeonhole currently retains only positivity and the
order `0 < a <= b <= 1`.  The constant side vector is a genuine occupied
dyadic shape with `a = b = 1`.  Consequently those current scalar outputs,
and even the literal definition of the adaptive proxy scale, cannot imply a
positive `delta`-power upper bound.  A thin-branch certificate must be
produced before (or together with) the occupied-bucket selection.
-/

/-- The dyadic label of the constant unit side vector. -/
def isotropicShapeLabel : Fin 3 -> Int := fun _ => 0

/-- The corresponding genuine positive side vector. -/
def isotropicSide : Fin 3 -> NNReal := fun _ => 1

@[simp] theorem sideShapeUpper_isotropicShapeLabel (i : Fin 3) :
    sideShapeUpper isotropicShapeLabel i = 1 := by
  apply NNReal.eq
  change dyadicCeilUpper 0 = (1 : Real)
  norm_num [dyadicCeilUpper]

/-- The isotropic label is not artificial: it is exactly the ceil-log label
of the positive constant unit side vector. -/
theorem sideShapeLabel_isotropicSide :
    sideShapeLabel isotropicSide = isotropicShapeLabel := by
  funext i
  norm_num [sideShapeLabel, isotropicSide, isotropicShapeLabel,
    dyadicCeilBucket, Real.logb]

@[simp] theorem bucketShortA_isotropicShapeLabel :
    bucketShortA isotropicShapeLabel = 1 := by
  simp [bucketShortA]

@[simp] theorem bucketShortB_isotropicShapeLabel :
    bucketShortB isotropicShapeLabel = 1 := by
  simp [bucketShortB]

/-- All scalar conclusions retained by the present occupied-bucket producer
hold for the isotropic label. -/
theorem isotropicShapeLabel_satisfies_current_bucket_outputs :
    0 < bucketShortA isotropicShapeLabel /\
      bucketShortA isotropicShapeLabel <= bucketShortB isotropicShapeLabel /\
      bucketShortB isotropicShapeLabel <= 1 := by
  norm_num

@[simp] theorem canonicalProxyScale_isotropic_one :
    selectedPlankFineCanonicalProxyScale 1 isotropicShapeLabel = 55296 := by
  apply NNReal.eq
  norm_num [selectedPlankFineCanonicalProxyScale,
    selectedPlankFineAxisLengthFloor]

/-- Concrete no-go for a callback-free power bound from the present bucket
outputs alone.  At unit parameters and exponent one, the genuine isotropic
label makes the canonical component (hence the max defining the adaptive
scale) at least `55296`, rather than at most `delta = 1`. -/
theorem current_bucket_outputs_do_not_force_adaptive_power_bound :
    Not (((selectedParentCenteredHalfPostAdaptiveProxyScale
        1 1 1 isotropicShapeLabel : NNReal) : ENNReal) ^ (1 : Real) <=
      (1 : ENNReal)) := by
  intro h
  rw [ENNReal.rpow_one] at h
  have hcanonical :
      (55296 : NNReal) <=
        selectedParentCenteredHalfPostAdaptiveProxyScale
          1 1 1 isotropicShapeLabel := by
    rw [<- canonicalProxyScale_isotropic_one]
    exact le_max_left _ _
  have hcanonicalENN :
      (55296 : ENNReal) <=
        ((selectedParentCenteredHalfPostAdaptiveProxyScale
          1 1 1 isotropicShapeLabel : NNReal) : ENNReal) := by
    exact_mod_cast hcanonical
  have : (55296 : ENNReal) <= 1 := hcanonicalENN.trans h
  norm_num at this

#print axioms sideShapeUpper_isotropicShapeLabel
#print axioms sideShapeLabel_isotropicSide
#print axioms bucketShortA_isotropicShapeLabel
#print axioms bucketShortB_isotropicShapeLabel
#print axioms isotropicShapeLabel_satisfies_current_bucket_outputs
#print axioms canonicalProxyScale_isotropic_one
#print axioms current_bucket_outputs_do_not_force_adaptive_power_bound

end
end Family8SelectedParentPlankCenteredAdaptiveScaleFlatnessAuditV4
