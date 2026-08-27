import ArchonPhysics.MeasurableOrderedHarmonicEnergy

/-!
# Local continuity of ordered projectors on the simple-spectrum locus

The totalized Lagrange projector is measurable on every Hermitian matrix but
cannot be continuous through an eigenvalue collision.  At a simple spectrum,
every denominator is nonzero.  The unconditional Weyl continuity of ordered
eigenvalues then makes every factor, their finite product, and every projector
entry locally continuous.

This is the deterministic stability input for localizing future quantitative
random-collision estimates to a spectral-gap event.  No probability estimate
for the complement of that event is asserted here.
-/

open scoped Matrix

namespace ArchonPhysics.SimpleSpectrumProjectorContinuity

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One Lagrange factor is locally continuous whenever its denominator is
nonzero at the base matrix. -/
theorem continuousAt_orderedModeFactor
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k j : Fin (Fintype.card ι)) (hjk : j ≠ k) :
    ContinuousAt (fun B : HermitianMatrix ι => orderedModeFactor B k j) A := by
  have hinv : ContinuousAt
      (fun B : HermitianMatrix ι =>
        (orderedEigenvalue B k - orderedEigenvalue B j)⁻¹) A :=
    ((continuous_orderedEigenvalue k).continuousAt.sub
      (continuous_orderedEigenvalue j).continuousAt).inv₀
        (sub_ne_zero.mpr (hsimple.ne (Ne.symm hjk)))
  have hval : Continuous (fun B : HermitianMatrix ι => B.1) :=
    continuous_subtype_val
  have hmatrix : ContinuousAt
      (fun B : HermitianMatrix ι =>
        matrixVal B - orderedEigenvalue B j • (1 : Matrix ι ι Real)) A := by
    exact hval.continuousAt.sub
      ((continuous_orderedEigenvalue j).smul continuous_const).continuousAt
  exact hinv.smul hmatrix

/-- A finite product of admissible Lagrange factors is locally continuous. -/
theorem continuousAt_orderedModeFactor_listProduct
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    ∀ L : List (Fin (Fintype.card ι)),
      (∀ j ∈ L, j ≠ k) →
      ContinuousAt (fun B : HermitianMatrix ι =>
        (L.map (orderedModeFactor B k)).prod) A
  | [], _h => continuousAt_const
  | j :: L, h => by
      simp only [List.map_cons, List.prod_cons]
      exact (continuousAt_orderedModeFactor A hsimple k j (h j (by simp))).mul
        (continuousAt_orderedModeFactor_listProduct A hsimple k L
          (fun l hl => h l (by simp [hl])))

/-- Every ordered rank-one projector is locally continuous at a simple
spectrum, as a matrix-valued function. -/
theorem continuousAt_orderedModeProjector
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    ContinuousAt (fun B : HermitianMatrix ι => orderedModeProjector B k) A := by
  unfold orderedModeProjector
  apply continuousAt_orderedModeFactor_listProduct A hsimple k
  intro j hj
  have hj' : j ∈ Finset.univ.erase k := by simpa using hj
  exact (Finset.mem_erase.mp hj').1

/-- Coordinate form of local projector continuity. -/
theorem continuousAt_orderedModeProjector_apply
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) (u v : ι) :
    ContinuousAt (fun B : HermitianMatrix ι => orderedModeProjector B k u v) A := by
  have heval : Continuous (fun P : Matrix ι ι Real => P u v) :=
    (continuous_apply v).comp (continuous_apply u)
  exact heval.continuousAt.comp
    (continuousAt_orderedModeProjector A hsimple k)

end

end ArchonPhysics.SimpleSpectrumProjectorContinuity
