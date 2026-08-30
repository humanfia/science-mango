import ArchonPhysics.FrozenAndersonDiagonalPotentialDensity

/-!
# Consumer: frozen Anderson diagonal-potential density
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
open MeasureTheory
open scoped ENNReal

noncomputable section

theorem problem_frozen_anderson_diagonal_potential_density
    {lambda : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda ≤
      ((3 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) •
        (volume : Measure Real) :=
  andersonDiagonalPotentialLaw_le_smul_volume hlambda

theorem problem_frozen_anderson_diagonal_potential_small_ball
    {lambda a b : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda (Set.Icc a b) ≤
      ((3 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) *
        ENNReal.ofReal (b - a) :=
  andersonDiagonalPotentialLaw_Icc_le hlambda

#print axioms problem_frozen_anderson_diagonal_potential_density
#print axioms problem_frozen_anderson_diagonal_potential_small_ball

end

end ArchonPhysicsConsumers.Thermalization
