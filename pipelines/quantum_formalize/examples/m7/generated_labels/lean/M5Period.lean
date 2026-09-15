import M5Foundation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Two

/-!
Definitions for M5 sections 1, 4 and 5. AdjoinRoot is the full polynomial
quotient, retaining nilpotents; no irreducibility assumption is imposed.
The definition is total. The experiment proves positivity under the actual
M5 assumptions, and proves that its value at F = 1 is 1.
-/
namespace M5
noncomputable def signaturePeriod (F : BinaryPolynomial) : ℕ :=
  orderOf (AdjoinRoot.root F)
end M5
