import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6

/-!
# Monotone expansion of a certified plank Cordoba factor, V5

Canonical successor to the failed elaboration/association drafts V1--V4.
This module freezes only the small monotonicity step used downstream.  It has
no selected-family or multiplicity hypothesis and preserves the genuine
container/popularity scale `A` verbatim.
-/

open scoped ENNReal NNReal

namespace Family8SelectedParentExactAssemblyCordobaExpandedV5

open Submission.Kakeya.ConvexGeometry
open Family8CertifiedPlankPairOverlapV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6

noncomputable section

set_option autoImplicit false
set_option warningAsError true

universe u

variable {iota : Type u} [Fintype iota]
variable {F : ConvexFamily iota} {C a b : NNReal}

/-- Multiplying the certified angle-level factor by the actual preceding
losses preserves the proved explicit dyadic angle-bucket bound. -/
theorem loss_mul_two_mul_certifiedPlankDyadicFactor_le_explicit
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (loss D A : ENNReal) :
    loss * (2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) D A) <=
      loss * (2 *
        (((certifiedPlankThresholdedAngleBucketLoss a b : Nat) : ENNReal) *
          D * A)) := by
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
    (certifiedPlankDyadicFactor_thresholded_le_explicit cert D A))

#print axioms
  loss_mul_two_mul_certifiedPlankDyadicFactor_le_explicit

end

end Family8SelectedParentExactAssemblyCordobaExpandedV5
