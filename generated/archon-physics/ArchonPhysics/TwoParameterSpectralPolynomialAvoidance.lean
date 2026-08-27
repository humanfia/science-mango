import ArchonPhysics.TwoParameterSpectralAveragingAtlas
import ArchonPhysics.InverseMassPolynomialAvoidance

/-!
# Polynomial degeneracy avoidance for two-mass spectral charts

The local-chart theorem in `TwoParameterSpectralAveragingAtlas` requires a
regular patch decomposition.  In the random-mass model, determinants and
discriminants obtained from finite transfer matrices are polynomial in finitely
many mass (or inverse-mass) coordinates.  This module specializes the existing
finite iid polynomial-avoidance theorem to the two-coordinate product law used
by a spectral chart: every nonzero polynomial degeneracy can be deleted at
zero iid-mass-pair measure.

This result proves nullity of an explicitly identified algebraic bad set.  It
does not assert that a proposed spectral Jacobian polynomial is nonzero; that
remains a concrete algebraic obligation for the model chart.
-/

namespace ArchonPhysics.TwoParameterSpectralPolynomialAvoidance

open Set MeasureTheory
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas

noncomputable section

/-- Repackage a pair of mass parameters as coordinates indexed by `Fin 2`. -/
def iidMassPairCoordinates (pair : Real × Real) : Fin 2 → Real :=
  MeasurableEquiv.finTwoArrow.symm pair

@[simp] theorem iidMassPairCoordinates_fst (pair : Real × Real) :
    iidMassPairCoordinates pair 0 = pair.1 := rfl

@[simp] theorem iidMassPairCoordinates_snd (pair : Real × Real) :
    iidMassPairCoordinates pair 1 = pair.2 := rfl

/-- A nonzero polynomial in two raw mass coordinates has a null zero set for
the iid mass-pair law.  This is the exact certificate used to remove an
algebraic Jacobian-degeneracy locus from a local spectral chart. -/
theorem iidMassPairLaw_zeroSet_mvPolynomial_eval
    (P : MvPolynomial (Fin 2) Real) (hP : P ≠ 0) :
    iidMassPairLaw
      {pair | MvPolynomial.eval (iidMassPairCoordinates pair) P = 0} = 0 := by
  have hpres := measurePreserving_finTwoArrow massCoordinateLaw
  have hsetMeas : MeasurableSet
      {pair : Real × Real |
        MvPolynomial.eval (iidMassPairCoordinates pair) P = 0} := by
    apply MeasurableSet.preimage (isClosed_singleton.measurableSet)
    exact P.continuous_eval.measurable.comp
      MeasurableEquiv.finTwoArrow.symm.measurable
  have hpreimage :
      MeasurableEquiv.finTwoArrow ⁻¹'
          {pair : Real × Real |
            MvPolynomial.eval (iidMassPairCoordinates pair) P = 0} =
        {coordinates : Fin 2 → Real |
          MvPolynomial.eval coordinates P = 0} := by
    ext coordinates
    change MvPolynomial.eval ![coordinates 0, coordinates 1] P = 0 ↔
      MvPolynomial.eval coordinates P = 0
    have hcoordinates : ![coordinates 0, coordinates 1] = coordinates := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinates]
  rw [iidMassPairLaw, ← hpres.map_eq,
    Measure.map_apply hpres.measurable hsetMeas, hpreimage]
  exact finiteMassLaw_zeroSet_mvPolynomial_eval P hP

/-- Repackage the coordinatewise inverse of a pair of raw masses. -/
def iidInverseMassPairCoordinates (pair : Real × Real) : Fin 2 → Real :=
  coordinatewiseInv (iidMassPairCoordinates pair)

@[simp] theorem iidInverseMassPairCoordinates_fst (pair : Real × Real) :
    iidInverseMassPairCoordinates pair 0 = pair.1⁻¹ := rfl

@[simp] theorem iidInverseMassPairCoordinates_snd (pair : Real × Real) :
    iidInverseMassPairCoordinates pair 1 = pair.2⁻¹ := rfl

/-- The same algebraic bad-set deletion is available when a spectral
Jacobian is polynomial in inverse masses, as happens for the weighted-cycle
representation of the harmonic operator. -/
theorem iidMassPairLaw_zeroSet_eval_inverseCoordinates
    (P : MvPolynomial (Fin 2) Real) (hP : P ≠ 0) :
    iidMassPairLaw
      {pair | MvPolynomial.eval (iidInverseMassPairCoordinates pair) P = 0} = 0 := by
  have hpres := measurePreserving_finTwoArrow massCoordinateLaw
  have hsetMeas : MeasurableSet
      {pair : Real × Real |
        MvPolynomial.eval (iidInverseMassPairCoordinates pair) P = 0} := by
    apply MeasurableSet.preimage (isClosed_singleton.measurableSet)
    exact P.continuous_eval.measurable.comp
      ((measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).inv).comp
        MeasurableEquiv.finTwoArrow.symm.measurable)
  have hpreimage :
      Set.preimage MeasurableEquiv.finTwoArrow
          {pair : Real × Real |
            MvPolynomial.eval (iidInverseMassPairCoordinates pair) P = 0} =
        {coordinates : Fin 2 → Real |
          MvPolynomial.eval (coordinatewiseInv coordinates) P = 0} := by
    ext coordinates
    change MvPolynomial.eval
        (coordinatewiseInv ![coordinates 0, coordinates 1]) P = 0 ↔
      MvPolynomial.eval (coordinatewiseInv coordinates) P = 0
    have hcoordinates : ![coordinates 0, coordinates 1] = coordinates := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinates]
  rw [iidMassPairLaw, ← hpres.map_eq,
    Measure.map_apply hpres.measurable hsetMeas, hpreimage]
  exact finiteMassLaw_zeroSet_eval_coordinatewiseInv P hP

end

end ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
