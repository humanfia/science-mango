import ArchonPhysics.NestedOscillatoryEnergyIdentity

/-!
# Consumer: exact nested return-energy identity

This consumer exposes the division-free identity equating the real return
time ordering with the squared one-step finite-time gain.  It is an exact
finite-time formula, not a kinetic-limit statement.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.NestedOscillatoryEnergyIdentity
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain

noncomputable section

/-- Consumer endpoint for the triangular shuffle identity. -/
theorem problem_nestedOscillatoryIntegral_add_swap
    (left right time : Real) :
    nestedOscillatoryIntegral left right time +
        nestedOscillatoryIntegral right left time =
      oscillatoryIntegral left time * oscillatoryIntegral right time :=
  nestedOscillatoryIntegral_add_swap left right time

/-- Consumer endpoint for the exact return-energy identity. -/
theorem problem_two_mul_re_nestedOscillatoryIntegral_neg_self
    (delta time : Real) :
    2 * (nestedOscillatoryIntegral (-delta) delta time).re =
      Complex.normSq (oscillatoryIntegral delta time) :=
  two_mul_re_nestedOscillatoryIntegral_neg_self delta time

#print axioms problem_nestedOscillatoryIntegral_add_swap
#print axioms problem_two_mul_re_nestedOscillatoryIntegral_neg_self

end

end ArchonPhysicsConsumers.Thermalization
