import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleCarrierV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1

open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1

noncomputable section

/-!
# Symmetric rectangle comparability for PYZ Lemma 5.5

PYZ Definition 3.2 quantifies over an arbitrary common enlarged graph
rectangle and is therefore symmetric.  The earlier
`leftGraphLambdaComparable` is a useful directed sufficient condition whose
container graph is forced to be the first graph; it is not the paper
relation itself.  This module records the honest common-container relation,
its symmetry/reflexivity at an actual equal scale, and the one-way bridge
from the directed proxy.
-/

/-- Literal PYZ comparability: two carriers fit in one common graph
rectangle of the exact enlarged base length and vertical radius. -/
def symmetricGraphLambdaComparable
    (R S : GraphRectangle) (delta t lambda : Real) : Prop :=
  exists container : GraphRectangle,
    container.right - container.left =
      Real.sqrt (lambda * delta / t) ∧
    R.carrier delta ∪ S.carrier delta ⊆
      container.carrier (lambda * delta)

/-- The common-container definition is symmetric without any geometric
side conditions. -/
theorem symmetricGraphLambdaComparable_symm
    {R S : GraphRectangle} {delta t lambda : Real}
    (h : symmetricGraphLambdaComparable R S delta t lambda) :
    symmetricGraphLambdaComparable S R delta t lambda := by
  rcases h with ⟨container, hlength, hcontain⟩
  refine ⟨container, hlength, ?_⟩
  simpa [union_comm] using hcontain

/-- An actual `(delta,t)` rectangle is comparable to itself at every
enlargement `lambda >= 1`. -/
theorem symmetricGraphLambdaComparable_refl_of_exact_length
    (R : GraphRectangle) {delta t lambda : Real}
    (hdelta : 0 <= delta) (ht : 0 < t) (hlambda : 1 <= lambda)
    (hlength : R.right - R.left = Real.sqrt (delta / t)) :
    symmetricGraphLambdaComparable R R delta t lambda := by
  have hdeltaLambda : delta <= lambda * delta := by
    calc
      delta = 1 * delta := by ring
      _ <= lambda * delta := mul_le_mul_of_nonneg_right hlambda hdelta
  have hratio : delta / t <= lambda * delta / t :=
    (div_le_div_iff_of_pos_right ht).2 hdeltaLambda
  have hsqrt : Real.sqrt (delta / t) <=
      Real.sqrt (lambda * delta / t) := Real.sqrt_le_sqrt hratio
  let container : GraphRectangle :=
    { graph := R.graph
      left := R.left
      right := R.left + Real.sqrt (lambda * delta / t)
      left_le_right := le_add_of_nonneg_right (Real.sqrt_nonneg _) }
  refine ⟨container, ?_, ?_⟩
  · simp [container]
  · intro q hq
    rcases hq with hq | hq
    · refine ⟨?_, ?_⟩
      · change q.2 ∈ Icc R.left
          (R.left + Real.sqrt (lambda * delta / t))
        have hqBase : q.2 ∈ R.base := hq.1
        constructor
        · exact hqBase.1
        · rw [← hlength] at hsqrt
          linarith [hqBase.2]
      · exact hq.2.trans hdeltaLambda
    · refine ⟨?_, ?_⟩
      · change q.2 ∈ Icc R.left
          (R.left + Real.sqrt (lambda * delta / t))
        have hqBase : q.2 ∈ R.base := hq.1
        constructor
        · exact hqBase.1
        · rw [← hlength] at hsqrt
          linarith [hqBase.2]
      · exact hq.2.trans hdeltaLambda

/-- The existing left-centered proxy supplies an honest common-container
witness.  The converse needs Lemma 3.12 geometry and is intentionally not
claimed here. -/
theorem symmetricGraphLambdaComparable_of_left
    {R S : GraphRectangle} {delta t lambda : Real}
    (h : leftGraphLambdaComparable R S delta t lambda) :
    symmetricGraphLambdaComparable R S delta t lambda := by
  rcases h with ⟨containerLeft, containerRight, hlength, hcontain⟩
  let container : GraphRectangle :=
    { graph := R.graph
      left := containerLeft
      right := containerRight
      left_le_right := by
        have hsqrt : 0 <= Real.sqrt (lambda * delta / t) :=
          Real.sqrt_nonneg _
        linarith }
  refine ⟨container, hlength, ?_⟩
  simpa [GraphRectangle.carrier, GraphRectangle.base, container] using hcontain

/-- Failure of honest symmetric comparability implies failure of the old
directed proxy in either orientation, which is the direction needed by the
existing rectangle-counting API. -/
theorem not_left_of_not_symmetricGraphLambdaComparable
    {R S : GraphRectangle} {delta t lambda : Real}
    (h : ¬ symmetricGraphLambdaComparable R S delta t lambda) :
    ¬ leftGraphLambdaComparable R S delta t lambda := by
  exact fun hleft => h (symmetricGraphLambdaComparable_of_left hleft)

theorem not_left_swap_of_not_symmetricGraphLambdaComparable
    {R S : GraphRectangle} {delta t lambda : Real}
    (h : ¬ symmetricGraphLambdaComparable R S delta t lambda) :
    ¬ leftGraphLambdaComparable S R delta t lambda := by
  exact not_left_of_not_symmetricGraphLambdaComparable
    (fun hswap => h (symmetricGraphLambdaComparable_symm hswap))

#print axioms symmetricGraphLambdaComparable
#print axioms symmetricGraphLambdaComparable_symm
#print axioms symmetricGraphLambdaComparable_refl_of_exact_length
#print axioms symmetricGraphLambdaComparable_of_left
#print axioms not_left_of_not_symmetricGraphLambdaComparable
#print axioms not_left_swap_of_not_symmetricGraphLambdaComparable

end

end FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1
