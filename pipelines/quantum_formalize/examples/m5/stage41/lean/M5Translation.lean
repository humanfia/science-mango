import M5FeasibleSource
import Mathlib.Data.Finset.Union

namespace M5.Translation

noncomputable def natSupport {N : ℕ} (S : Finset (ZMod N)) : Finset ℕ := by
  classical
  exact S.image ZMod.val

noncomputable def shift {N : ℕ} (S : Finset (ZMod N)) (c : ZMod N) : Finset (ZMod N) := by
  classical
  exact S.image (fun x => x + c)

noncomputable def differences {N : ℕ} (S : Finset (ZMod N)) : Finset (ZMod N) := by
  classical
  exact S.biUnion (fun x => S.image (fun y => x - y))

noncomputable def differenceGcd {N : ℕ} (S U : Finset (ZMod N)) : ℕ :=
  M5.Connectivity.supportGcd N (natSupport (differences S)) (natSupport (differences U))

noncomputable def supportPolynomial {N : ℕ} (S : Finset (ZMod N)) : M5.BinaryPolynomial :=
  M5.SupportPolynomial.ofSupport (natSupport S)

end M5.Translation
