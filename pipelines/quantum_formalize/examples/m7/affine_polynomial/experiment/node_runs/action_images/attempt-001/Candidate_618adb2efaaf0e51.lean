import FrozenTarget_618adb2efaaf0e51
theorem M7.AffinePolynomial.action_images : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  have hleft := M7.AffinePolynomial.image_affine N g.unit g.leftShift (if g.exchange then c.2 else c.1)
  have hright := M7.AffinePolynomial.image_affine N g.unit g.rightShift (if g.exchange then c.1 else c.2)
  cases h : g.exchange <;>
    simpa [M7.Action.act, M7.AffinePolynomial.shifted, h] using And.intro hleft hright
