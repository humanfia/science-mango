import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2

/-!
# A same-assembly Core-native frozen third-factor bundle

This small record freezes the selected coarse indices and the literal
Section-8 `middleScale -> 1` estimate on one frozen assembly.  Its numerical
projections match the `thirdCount`, `thirdAverage`, `thirdLoss`, and `hThird`
fields consumed by the long-core three-scale data package.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CoreNativeFrozenThirdBundleV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

variable {iota kappa : Type} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {G : ConvexFamily kappa}

/-- A frozen third-factor estimate on one literal factorization and one
literal assembly. -/
structure CoreNativeFrozenThirdBundle
    (Q : ConvexFactorization F G) (Y : Shading F)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (middleScale : NNReal) (loss : ENNReal) (gamma : Real) where
  selected : Finset kappa
  selected_nonempty : selected.Nonempty
  bound : A.frozenCoarse.averageMultiplicity <=
    loss * sectionEightScaleCountFrostmanFactor
      middleScale 1 (Fintype.card kappa) gamma

namespace CoreNativeFrozenThirdBundle

def thirdCount
    {Q : ConvexFactorization F G} {Y : Shading F}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {middleScale : NNReal} {loss : ENNReal} {gamma : Real}
    (_X : CoreNativeFrozenThirdBundle Q Y A middleScale loss gamma) : Nat :=
  Fintype.card kappa

def thirdAverage
    {Q : ConvexFactorization F G} {Y : Shading F}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {middleScale : NNReal} {loss : ENNReal} {gamma : Real}
    (_X : CoreNativeFrozenThirdBundle Q Y A middleScale loss gamma) : ENNReal :=
  A.frozenCoarse.averageMultiplicity

def thirdLoss
    {Q : ConvexFactorization F G} {Y : Shading F}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {middleScale : NNReal} {loss : ENNReal} {gamma : Real}
    (_X : CoreNativeFrozenThirdBundle Q Y A middleScale loss gamma) : ENNReal :=
  loss

theorem hThird
    {Q : ConvexFactorization F G} {Y : Shading F}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {middleScale : NNReal} {loss : ENNReal} {gamma : Real}
    (X : CoreNativeFrozenThirdBundle Q Y A middleScale loss gamma) :
    X.thirdAverage <= X.thirdLoss *
      sectionEightScaleCountFrostmanFactor
        middleScale 1 X.thirdCount gamma :=
  X.bound

#print axioms CoreNativeFrozenThirdBundle
#print axioms thirdCount
#print axioms thirdAverage
#print axioms thirdLoss
#print axioms hThird

end CoreNativeFrozenThirdBundle
end
end Family8CoreNativeFrozenThirdBundleV1
