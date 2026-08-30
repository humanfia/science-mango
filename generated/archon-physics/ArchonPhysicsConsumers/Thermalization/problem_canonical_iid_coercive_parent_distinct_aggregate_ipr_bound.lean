import ArchonPhysics.CanonicalIIDCoerciveParentDistinctAggregateIPRBound

/-!
# Consumer: aggregate control and orthogonality obstruction

This consumer checks the replacement of a uniform modewise IPR premise by
the actual mode-averaged parent-distinct collision weight and, more loosely,
by root-averaged off-diagonal cubic mass or mean IPR.  Its canonical limit
theorem keeps decay of the averaged collision weight as an explicit premise.

The replicated rational frame certifies that orthogonality alone cannot
produce a volume-decaying estimate: its naturally averaged off-diagonal mass
is `144 / 625` at every positive block count.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalIIDCoerciveParentDistinctAggregateIPRBound

noncomputable section

/-- Consumer alias for rootwise Parseval after deleting the diagonal mode. -/
theorem problem_rootOffDiagonalRepeatedCubicMass_le_ipr :
    type_of% (@rootOffDiagonalRepeatedCubicMass_le_ipr) :=
  @rootOffDiagonalRepeatedCubicMass_le_ipr

/-- Consumer alias for the averaged Parseval estimate. -/
theorem problem_meanOffDiagonalRepeatedCubicMass_le_meanIPR :
    type_of% (@meanOffDiagonalRepeatedCubicMass_le_meanIPR) :=
  @meanOffDiagonalRepeatedCubicMass_le_meanIPR

/-- Consumer alias for the actual collision-network comparison. -/
theorem problem_meanInteractionWeight_le_meanOffDiagonal :
    type_of%
      (@harmonicMeanParentDistinctChildRepeatedInteractionWeight_le_meanOffDiagonal) :=
  @harmonicMeanParentDistinctChildRepeatedInteractionWeight_le_meanOffDiagonal

/-- Consumer alias for the exact kinetic-time averaged-network bound. -/
theorem problem_parentDistinct_at_kineticTime_le_meanInteractionWeight :
    type_of%
      (@physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_meanInteractionWeight) :=
  @physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_meanInteractionWeight

/-- Consumer alias for canonical convergence under the displayed averaged
collision-network decay premise. -/
theorem problem_canonical_parentDistinct_tendsto_zero_of_meanInteractionWeight :
    type_of%
      (@canonical_parentDistinct_at_kineticTime_tendsto_zero_of_meanInteractionWeight) :=
  @canonical_parentDistinct_at_kineticTime_tendsto_zero_of_meanInteractionWeight

/-- Consumer alias for exact orthogonality of the arbitrary-volume block
frame. -/
theorem problem_replicatedRationalRotationFrame_orthonormal :
    type_of% (@replicatedRationalRotationFrame_orthonormal) :=
  @replicatedRationalRotationFrame_orthonormal

/-- Consumer alias for the sharp no-volume-decay obstruction. -/
theorem problem_meanOffDiagonal_replicatedRationalRotationFrame :
    type_of%
      (@meanOffDiagonalRepeatedCubicMass_replicatedRationalRotationFrame) :=
  @meanOffDiagonalRepeatedCubicMass_replicatedRationalRotationFrame

#print axioms rootOffDiagonalRepeatedCubicMass_le_ipr
#print axioms meanOffDiagonalRepeatedCubicMass_le_meanIPR
#print axioms
  harmonicMeanParentDistinctChildRepeatedInteractionWeight_le_meanOffDiagonal
#print axioms
  physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_meanInteractionWeight
#print axioms
  canonical_parentDistinct_at_kineticTime_tendsto_zero_of_meanInteractionWeight
#print axioms replicatedRationalRotationFrame_orthonormal
#print axioms
  meanOffDiagonalRepeatedCubicMass_replicatedRationalRotationFrame
#print axioms
  problem_canonical_parentDistinct_tendsto_zero_of_meanInteractionWeight

end

end ArchonPhysicsConsumers.Thermalization
