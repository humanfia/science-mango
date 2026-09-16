import M8MixedFamilyAccepted
namespace M8.MixedNonproduct
noncomputable def Cycles {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Set (M6.Physical.Word N) :=
  {z | M6.Physical.syndrome N (M7.Supports.indicator c.1) (M7.Supports.indicator c.2) z = 0}
def Product {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Prop :=
  ∃ U V : Set (M6.Physical.Block N), Cycles c = U ×ˢ V
def wordAction {N : ℕ} [NeZero N] (g : M7.Action.Record N) (z : M6.Physical.Word N) :=
  M6.RecipeIsometries.translateWord N g.leftShift g.rightShift
    (M6.RecipeIsometries.multiplyWord N g.unit (if g.exchange then M6.RecipeIsometries.exchange N z else z))
end M8.MixedNonproduct
