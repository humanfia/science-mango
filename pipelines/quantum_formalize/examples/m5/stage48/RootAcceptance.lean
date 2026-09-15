-- Instantiate the import with the final promoted root proof module only after its acceptance.
import M5OriginalRootAccepted

example : ∀ (w : ℕ) (F : M5.BinaryPolynomial),
    0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Spec w F :=
  M5.Final.original_m5

#print axioms M5.Final.original_m5
