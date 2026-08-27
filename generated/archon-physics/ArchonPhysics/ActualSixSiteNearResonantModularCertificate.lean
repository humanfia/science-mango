import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Standalone modular certificate for the six-site collision weight

This module contains only finite computations over `ZMod 103`.  Keeping the
certificate separate prevents native code generation from closing over the
physics development.
-/

open scoped BigOperators

namespace ArchonPhysics.ActualSixSiteNearResonantModularCertificate

abbrev FlatIndex := Fin 125
abbrev CubeIndex := Fin 5 × (Fin 5 × Fin 5)

def flattenIndex (a : CubeIndex) : FlatIndex :=
  ⟨a.1.val * 25 + a.2.1.val * 5 + a.2.2.val, by omega⟩

def residualCoeffArray103 : Array (ZMod 103) := #[
    102, 10, 85, 27, 93, 10, 58, 86, 69, 7, 85, 86, 88, 21, 38,
    27, 69, 21, 35, 31, 93, 7, 38, 31, 21, 10, 58, 86, 69, 7,
    58, 79, 46, 95, 65, 86, 46, 83, 95, 41, 69, 95, 95, 93, 86,
    7, 65, 41, 86, 75, 85, 86, 88, 21, 38, 86, 46, 83, 95, 41,
    88, 83, 28, 58, 69, 21, 95, 58, 25, 32, 38, 41, 69, 32, 69,
    27, 69, 21, 35, 31, 69, 95, 95, 93, 86, 21, 95, 58, 25, 32,
    35, 93, 25, 40, 55, 31, 86, 32, 55, 2, 93, 7, 38, 31, 21,
    7, 65, 41, 86, 75, 38, 41, 69, 32, 69, 31, 86, 32, 55, 2,
    21, 75, 69, 2, 41
  ]

def inverseCoeffArray103 : Array (ZMod 103) := #[
    80, 91, 98, 87, 96, 91, 52, 59, 86, 56, 98, 59, 41, 42, 80,
    87, 86, 42, 42, 33, 96, 56, 80, 33, 52, 91, 52, 59, 86, 56,
    52, 4, 40, 2, 36, 59, 40, 12, 85, 77, 86, 2, 85, 72, 96,
    56, 36, 77, 96, 38, 98, 59, 41, 42, 80, 59, 40, 12, 85, 77,
    41, 12, 1, 60, 92, 42, 85, 60, 37, 31, 80, 77, 92, 31, 90,
    87, 86, 42, 42, 33, 86, 2, 85, 72, 96, 42, 85, 60, 37, 31,
    42, 72, 37, 70, 2, 33, 96, 31, 2, 75, 96, 56, 80, 33, 52,
    56, 36, 77, 96, 38, 80, 77, 92, 31, 90, 33, 96, 31, 2, 75,
    52, 38, 90, 75, 19
  ]

def residualCoeff103 (i : FlatIndex) : ZMod 103 :=
  residualCoeffArray103[i.val]'(by change i.val < 125; exact i.isLt)

def inverseCoeff103 (i : FlatIndex) : ZMod 103 :=
  inverseCoeffArray103[i.val]'(by change i.val < 125; exact i.isLt)

def residualCube103 (a : CubeIndex) : ZMod 103 :=
  residualCoeff103 (flattenIndex a)

def inverseCube103 (a : CubeIndex) : ZMod 103 :=
  inverseCoeff103 (flattenIndex a)

def reducedPowerArray103 : Array (ZMod 103) := #[
    1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 27, 23, 89, 83, 11,
    91, 74, 75, 75, 101, 49, 45, 102, 12, 53, 92, 32, 24, 72, 80
  ]

def reducedPower103 (n : Fin 9) (i : Fin 5) : ZMod 103 :=
  reducedPowerArray103[n.val * 5 + i.val]'(
    by change n.val * 5 + i.val < 45; omega)

def origin : CubeIndex := (0, (0, 0))

end ArchonPhysics.ActualSixSiteNearResonantModularCertificate
