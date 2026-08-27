import Mathlib.Analysis.Calculus.Deriv.Basic
import ArchonPhysics.MeasurableOrderedEigenframe

/-!
# Hellmann--Feynman identity for finite real Hermitian curves

This module derives the eigenvalue derivative from a differentiated,
normalized eigenpair without choosing a global eigenvector phase.
-/

open scoped Matrix

namespace ArchonPhysics.OrderedEigenvalueHellmannFeynman

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.MeasurableOrderedModeCoupling
open Filter

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Algebraic Hellmann--Feynman cancellation after differentiating an
eigenpair equation. -/
theorem eigenvalueDerivative_eq_quadraticForm_of_differentiated_eigenpair
    (A dA : Matrix ι ι Real) (lambda dlambda : Real)
    (u du : ι → Real) (hA : A.IsHermitian)
    (heigen : A *ᵥ u = lambda • u)
    (hnormalized : u ⬝ᵥ u = 1)
    (hdifferentiated :
      dA *ᵥ u + A *ᵥ du = dlambda • u + lambda • du) :
    dlambda = u ⬝ᵥ (dA *ᵥ u) := by
  have htranspose : A.transpose = A := by
    ext i j
    have hij := congrArg (fun M : Matrix ι ι Real => M i j) hA
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hij
  have hmove : u ⬝ᵥ (A *ᵥ du) = lambda * (u ⬝ᵥ du) := by
    calc
      u ⬝ᵥ (A *ᵥ du) = (u ᵥ* A) ⬝ᵥ du :=
        Matrix.dotProduct_mulVec u A du
      _ = (A.transpose *ᵥ u) ⬝ᵥ du := by
        rw [Matrix.mulVec_transpose]
      _ = (A *ᵥ u) ⬝ᵥ du := by rw [htranspose]
      _ = (lambda • u) ⬝ᵥ du := by rw [heigen]
      _ = lambda * (u ⬝ᵥ du) := by simp
  have hdot := congrArg (fun value : ι → Real => u ⬝ᵥ value)
    hdifferentiated
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hdot
  rw [hmove, hnormalized] at hdot
  linarith

/-- Coordinatewise calculus turns an eventually valid eigenpair equation
into its exact differentiated vector equation. -/
theorem differentiated_eigenpair_equation
    (matrix : Real → Matrix ι ι Real)
    (eigenvalue : Real → Real) (eigenvector : Real → ι → Real)
    (x : Real) (matrixDerivative : Matrix ι ι Real)
    (eigenvalueDerivative : Real) (eigenvectorDerivative : ι → Real)
    (hmatrix : ∀ i j, HasDerivAt
      (fun t => matrix t i j) (matrixDerivative i j) x)
    (heigenvalue : HasDerivAt eigenvalue eigenvalueDerivative x)
    (heigenvector : ∀ i, HasDerivAt
      (fun t => eigenvector t i) (eigenvectorDerivative i) x)
    (heigenpair : ∀ᶠ t in nhds x,
      matrix t *ᵥ eigenvector t = eigenvalue t • eigenvector t) :
    matrixDerivative *ᵥ eigenvector x +
        matrix x *ᵥ eigenvectorDerivative =
      eigenvalueDerivative • eigenvector x +
        eigenvalue x • eigenvectorDerivative := by
  ext i
  let leftDerivative : Real :=
    ∑ j, (matrixDerivative i j * eigenvector x j +
      matrix x i j * eigenvectorDerivative j)
  let rightDerivative : Real :=
    eigenvalueDerivative * eigenvector x i +
      eigenvalue x * eigenvectorDerivative i
  have hleft : HasDerivAt
      (∑ j, (fun t => matrix t i j) * (fun t => eigenvector t j))
      leftDerivative x := by
    simpa [leftDerivative] using HasDerivAt.sum (u := Finset.univ)
      (fun j _hj => (hmatrix i j).mul (heigenvector j))
  have hright : HasDerivAt
      (eigenvalue * fun t => eigenvector t i)
      rightDerivative x := by
    simpa [rightDerivative] using heigenvalue.mul (heigenvector i)
  have heq :
      (∑ j, (fun t => matrix t i j) * (fun t => eigenvector t j)) =ᶠ[nhds x]
        eigenvalue * fun t => eigenvector t i := by
    filter_upwards [heigenpair] with t ht
    have hcoordinate := congrFun ht i
    simpa [Matrix.mulVec, dotProduct] using hcoordinate
  have hderivative : leftDerivative = rightDerivative :=
    (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simpa [leftDerivative, rightDerivative, Matrix.mulVec, dotProduct,
    Finset.sum_add_distrib] using hderivative


section ProjectorBranch

variable [DecidableEq ι]

/-- Every entry of one Lagrange projector factor is differentiable along a
differentiable Hermitian curve at a simple-spectrum point. -/
theorem differentiableAt_orderedModeFactor_apply
    (sample : Real → HermitianMatrix ι) (x : Real)
    (hsimple : SimpleOrderedSpectrum (sample x))
    (hmatrix : ∀ i j, DifferentiableAt Real
      (fun t => (sample t).1 i j) x)
    (heigenvalue : ∀ r, DifferentiableAt Real
      (fun t => orderedEigenvalue (sample t) r) x)
    (k j : Fin (Fintype.card ι)) (hjk : j ≠ k) (a b : ι) :
    DifferentiableAt Real
      (fun t => orderedModeFactor (sample t) k j a b) x := by
  have hgap : DifferentiableAt Real
      (fun t => orderedEigenvalue (sample t) k -
        orderedEigenvalue (sample t) j) x :=
    (heigenvalue k).sub (heigenvalue j)
  have hgapNe :
      orderedEigenvalue (sample x) k -
        orderedEigenvalue (sample x) j ≠ 0 :=
    sub_ne_zero.mpr (hsimple.ne hjk.symm)
  change DifferentiableAt Real
    (fun t =>
      (orderedEigenvalue (sample t) k -
          orderedEigenvalue (sample t) j)⁻¹ *
        ((sample t).1 a b - orderedEigenvalue (sample t) j *
          (1 : Matrix ι ι Real) a b)) x
  apply (hgap.inv hgapNe).mul
  exact (hmatrix a b).sub
    ((heigenvalue j).mul
      (differentiableAt_const ((1 : Matrix ι ι Real) a b)))


/-- A finite product of Lagrange factors is entrywise differentiable when
every listed factor avoids the selected mode. -/
theorem differentiableAt_orderedModeFactorListProduct_apply
    (sample : Real → HermitianMatrix ι) (x : Real)
    (hsimple : SimpleOrderedSpectrum (sample x))
    (hmatrix : ∀ i j, DifferentiableAt Real
      (fun t => (sample t).1 i j) x)
    (heigenvalue : ∀ r, DifferentiableAt Real
      (fun t => orderedEigenvalue (sample t) r) x)
    (k : Fin (Fintype.card ι)) :
    ∀ (L : List (Fin (Fintype.card ι))),
      (∀ j ∈ L, j ≠ k) → ∀ a b : ι,
      DifferentiableAt Real
        (fun t => (L.map (orderedModeFactor (sample t) k)).prod a b) x
  | [], _hL, a, b => by
      simp
  | j :: L, hL, a, b => by
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      have hsum := DifferentiableAt.sum (u := Finset.univ)
        (fun q _hq =>
          (differentiableAt_orderedModeFactor_apply sample x hsimple
            hmatrix heigenvalue k j (hL j (by simp)) a q).mul
          (differentiableAt_orderedModeFactorListProduct_apply sample x
            hsimple hmatrix heigenvalue k L
            (fun r hr => hL r (by simp [hr])) q b))
      have hfunction :
          (fun t => ∑ q, orderedModeFactor (sample t) k j a q *
            (L.map (orderedModeFactor (sample t) k)).prod q b) =
            ∑ q, (fun t => orderedModeFactor (sample t) k j a q *
              (L.map (orderedModeFactor (sample t) k)).prod q b) := by
        funext t
        simp
      rw [hfunction]
      exact hsum

/-- The complete ordered Lagrange projector is entrywise differentiable at
every differentiable simple-spectrum point. -/
theorem differentiableAt_orderedModeProjector_apply
    (sample : Real → HermitianMatrix ι) (x : Real)
    (hsimple : SimpleOrderedSpectrum (sample x))
    (hmatrix : ∀ i j, DifferentiableAt Real
      (fun t => (sample t).1 i j) x)
    (heigenvalue : ∀ r, DifferentiableAt Real
      (fun t => orderedEigenvalue (sample t) r) x)
    (k : Fin (Fintype.card ι)) (a b : ι) :
    DifferentiableAt Real
      (fun t => orderedModeProjector (sample t) k a b) x := by
  unfold orderedModeProjector
  apply differentiableAt_orderedModeFactorListProduct_apply
    sample x hsimple hmatrix heigenvalue k
  intro j hj
  have hmem : j ∈ Finset.univ.erase k := by simpa using hj
  exact (Finset.mem_erase.mp hmem).1


/-- Apply the moving ordered projector to the fixed normalized eigenvector
at the base point.  This removes global sign choices while retaining a local
eigenvector branch. -/
def anchoredOrderedEigenvector
    (sample : Real → HermitianMatrix ι) (x : Real)
    (k : Fin (Fintype.card ι)) (t : Real) : ι → Real :=
  orderedModeProjector (sample t) k *ᵥ
    ⇑((sample x).2.eigenvectorBasis (orderedIndexEquiv k))

theorem differentiableAt_anchoredOrderedEigenvector_apply
    (sample : Real → HermitianMatrix ι) (x : Real)
    (hsimple : SimpleOrderedSpectrum (sample x))
    (hmatrix : ∀ i j, DifferentiableAt Real
      (fun t => (sample t).1 i j) x)
    (heigenvalue : ∀ r, DifferentiableAt Real
      (fun t => orderedEigenvalue (sample t) r) x)
    (k : Fin (Fintype.card ι)) (a : ι) :
    DifferentiableAt Real
      (fun t => anchoredOrderedEigenvector sample x k t a) x := by
  let base : ι → Real :=
    ⇑((sample x).2.eigenvectorBasis (orderedIndexEquiv k))
  have hsum := DifferentiableAt.sum (u := Finset.univ)
    (fun b _hb =>
      (differentiableAt_orderedModeProjector_apply sample x hsimple
        hmatrix heigenvalue k a b).mul
        (differentiableAt_const (base b)))
  have hfunction :
      (fun t => anchoredOrderedEigenvector sample x k t a) =
        ∑ b, (fun t => orderedModeProjector (sample t) k a b * base b) := by
    funext t
    simp [anchoredOrderedEigenvector, Matrix.mulVec, dotProduct, base]
  rw [hfunction]
  exact hsum

/-- At the base point the anchored branch is the normalized matching
eigenvector itself. -/
theorem anchoredOrderedEigenvector_self
    (sample : Real → HermitianMatrix ι) (x : Real)
    (hsimple : SimpleOrderedSpectrum (sample x))
    (k : Fin (Fintype.card ι)) :
    anchoredOrderedEigenvector sample x k x =
      ⇑((sample x).2.eigenvectorBasis (orderedIndexEquiv k)) := by
  unfold anchoredOrderedEigenvector
  rw [orderedModeProjector_mulVec_eigenvectorBasis
    (sample x) hsimple k k]
  simp

/-- Wherever the ordered spectrum stays simple, the anchored branch obeys
the exact moving eigenpair equation. -/
theorem eventually_anchoredOrderedEigenvector_eigenpair
    (sample : Real → HermitianMatrix ι) (x : Real)
    (k : Fin (Fintype.card ι))
    (hsimpleEventually : ∀ᶠ t in nhds x,
      SimpleOrderedSpectrum (sample t)) :
    ∀ᶠ t in nhds x,
      matrixVal (sample t) *ᵥ anchoredOrderedEigenvector sample x k t =
        orderedEigenvalue (sample t) k •
          anchoredOrderedEigenvector sample x k t := by
  filter_upwards [hsimpleEventually] with t hsimple
  let base : ι → Real :=
    ⇑((sample x).2.eigenvectorBasis (orderedIndexEquiv k))
  have happ := congrArg (fun M : Matrix ι ι Real => M *ᵥ base)
    (matrixVal_mul_orderedModeProjector (sample t) hsimple k)
  simpa [anchoredOrderedEigenvector, base, Matrix.mulVec_mulVec,
    Matrix.smul_mulVec] using happ

/-- Hellmann--Feynman for a locally simple ordered eigenvalue branch.  The
projector construction supplies a differentiable normalized eigenvector
branch, so no eigenvector phase choice is assumed. -/
theorem orderedEigenvalueDerivative_eq_quadraticForm
    (sample : Real → HermitianMatrix ι) (x : Real)
    (hsimple : SimpleOrderedSpectrum (sample x))
    (hsimpleEventually : ∀ᶠ t in nhds x,
      SimpleOrderedSpectrum (sample t))
    (matrixDerivative : Matrix ι ι Real)
    (hmatrix : ∀ i j, HasDerivAt
      (fun t => (sample t).1 i j) (matrixDerivative i j) x)
    (heigenvalueDifferentiable : ∀ r, DifferentiableAt Real
      (fun t => orderedEigenvalue (sample t) r) x)
    (k : Fin (Fintype.card ι)) (eigenvalueDerivative : Real)
    (heigenvalue : HasDerivAt
      (fun t => orderedEigenvalue (sample t) k)
      eigenvalueDerivative x) :
    eigenvalueDerivative =
      ⇑((sample x).2.eigenvectorBasis (orderedIndexEquiv k)) ⬝ᵥ
        (matrixDerivative *ᵥ
          ⇑((sample x).2.eigenvectorBasis (orderedIndexEquiv k))) := by
  let branch : Real → ι → Real :=
    anchoredOrderedEigenvector sample x k
  let branchDerivative : ι → Real := fun i =>
    deriv (fun t => branch t i) x
  have hmatrixDifferentiable : ∀ i j, DifferentiableAt Real
      (fun t => (sample t).1 i j) x := fun i j =>
    (hmatrix i j).differentiableAt
  have hbranchDifferentiable (i : ι) : DifferentiableAt Real
      (fun t => branch t i) x := by
    simpa [branch] using
      (differentiableAt_anchoredOrderedEigenvector_apply sample x hsimple
        hmatrixDifferentiable heigenvalueDifferentiable k i)
  have hbranchDerivative (i : ι) : HasDerivAt
      (fun t => branch t i) (branchDerivative i) x := by
    simpa [branchDerivative] using (hbranchDifferentiable i).hasDerivAt
  have hdifferentiated :
      matrixDerivative *ᵥ branch x +
          matrixVal (sample x) *ᵥ branchDerivative =
        eigenvalueDerivative • branch x +
          orderedEigenvalue (sample x) k • branchDerivative := by
    apply differentiated_eigenpair_equation
      (matrix := fun t => matrixVal (sample t))
      (eigenvalue := fun t => orderedEigenvalue (sample t) k)
      (eigenvector := branch)
    · intro i j
      simpa [matrixVal] using hmatrix i j
    · exact heigenvalue
    · exact hbranchDerivative
    · simpa [branch] using
        eventually_anchoredOrderedEigenvector_eigenpair sample x k
          hsimpleEventually
  have hbranchSelf : branch x =
      ⇑((sample x).2.eigenvectorBasis (orderedIndexEquiv k)) := by
    simpa [branch] using anchoredOrderedEigenvector_self sample x hsimple k
  have heigen : matrixVal (sample x) *ᵥ branch x =
      orderedEigenvalue (sample x) k • branch x := by
    rw [hbranchSelf]
    exact matrixVal_mulVec_eigenvectorBasis (sample x) k
  have hnormalized : branch x ⬝ᵥ branch x = 1 := by
    rw [hbranchSelf]
    have hinner := (sample x).2.eigenvectorBasis.inner_eq_one
      (orderedIndexEquiv k)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      using hinner
  have hHF := eigenvalueDerivative_eq_quadraticForm_of_differentiated_eigenpair
    (matrixVal (sample x)) matrixDerivative
    (orderedEigenvalue (sample x) k) eigenvalueDerivative
    (branch x) branchDerivative (sample x).2 heigen hnormalized hdifferentiated
  simpa [hbranchSelf] using hHF

/-- A rank-one matrix direction evaluates on a simple ordered mode as the
basis-free quadratic weight of that mode's spectral projector. -/
theorem quadraticForm_smul_vecMulVec_eq_projectorWeight
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) (c : Real) (v : ι → Real) :
    ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) ⬝ᵥ
        ((c • Matrix.vecMulVec v v) *ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k))) =
      c * (v ⬝ᵥ (orderedModeProjector A k *ᵥ v)) := by
  rw [orderedModeProjector_eq_vecMulVec A hsimple k,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm
    ⇑(A.2.eigenvectorBasis (orderedIndexEquiv k)) v]

/-- Hellmann--Feynman specialized to a rank-one perturbation direction,
expressed entirely through the ordered spectral projector. -/
theorem orderedEigenvalueDerivative_eq_projectorWeight
    (sample : Real → HermitianMatrix ι) (x : Real)
    (hsimple : SimpleOrderedSpectrum (sample x))
    (hsimpleEventually : ∀ᶠ t in nhds x,
      SimpleOrderedSpectrum (sample t))
    (c : Real) (v : ι → Real)
    (hmatrix : ∀ i j, HasDerivAt
      (fun t => (sample t).1 i j)
      ((c • Matrix.vecMulVec v v) i j) x)
    (heigenvalueDifferentiable : ∀ r, DifferentiableAt Real
      (fun t => orderedEigenvalue (sample t) r) x)
    (k : Fin (Fintype.card ι)) (eigenvalueDerivative : Real)
    (heigenvalue : HasDerivAt
      (fun t => orderedEigenvalue (sample t) k)
      eigenvalueDerivative x) :
    eigenvalueDerivative =
      c * (v ⬝ᵥ (orderedModeProjector (sample x) k *ᵥ v)) := by
  rw [orderedEigenvalueDerivative_eq_quadraticForm sample x hsimple
    hsimpleEventually (c • Matrix.vecMulVec v v) hmatrix
    heigenvalueDifferentiable k eigenvalueDerivative heigenvalue]
  exact quadraticForm_smul_vecMulVec_eq_projectorWeight
    (sample x) hsimple k c v

end ProjectorBranch

end

end ArchonPhysics.OrderedEigenvalueHellmannFeynman
