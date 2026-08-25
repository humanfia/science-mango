import FamilyStickyGrounding.FamilyStickyScaleChainAdjacentUpperProducerV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainTerminalFiniteSearchV1

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesChainAtEveryAdapterV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainAdjacentUpperProducerV1

noncomputable section

/-!
# Sticky Kakeya: finite search producer for terminal no-split

The terminal condition ranges over a continuum of `NNReal` scales.  This
module separates the two ingredients needed to certify it without storing
that conclusion as a field:

* a finite, threshold-free enumeration of every buffered candidate scale;
* actual lower inequalities checked only on that finite enumeration.

The selector computes the least bad candidate.  Its soundness and minimality
are proved before an empty selection is transported, using completeness, to
the terminal no-split statement.
-/

variable {delta : NNReal} {outerDepth : Nat} {epsilon : Real}
  {eta : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta outerDepth}

/-- The literal Katz--Tao splitting threshold at an intermediate scale. -/
def splitThreshold (S : FiniteScaleSequence delta outerDepth)
    (eta : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (rho : NNReal) : ENNReal :=
  (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage)

/-- An actual bad scale: it lies in the buffered interval and the literal
coarse Delta-max falls strictly below the next exponent threshold. -/
def IsBadScale (A : ActualIntervalCovers S) (epsilon : Real)
    (eta : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (rho : NNReal) : Prop :=
  S.IsBuffered epsilon m rho ∧
    A.coarseValueAt m rho < splitThreshold S eta stage m rho

/-- A finite scale enumeration.  Completeness contains no concentration,
exponent, or threshold statement. -/
structure CandidateSearch (A : ActualIntervalCovers S)
    (epsilon : Real) (eta : Nat -> Real) (stage : Nat) where
  candidates : Fin outerDepth -> Finset NNReal
  buffered_complete : forall m rho,
    S.IsBuffered epsilon m rho -> rho ∈ candidates m

namespace CandidateSearch

variable {A : ActualIntervalCovers S}
  (Q : CandidateSearch A epsilon eta stage)

/-- The finite subset on which the actual strict splitting inequality holds. -/
def badCandidates (m : Fin outerDepth) : Finset NNReal := by
  classical
  exact (Q.candidates m).filter
    (IsBadScale A epsilon eta stage m)

@[simp] theorem mem_badCandidates (m : Fin outerDepth) (rho : NNReal) :
    rho ∈ Q.badCandidates m <->
      rho ∈ Q.candidates m ∧
        IsBadScale A epsilon eta stage m rho := by
  classical
  simp [badCandidates]

/-- Computable finite search result: the least actual bad candidate, if one
exists. -/
def selectedBadScale (m : Fin outerDepth) : Option NNReal :=
  if h : (Q.badCandidates m).Nonempty then
    some ((Q.badCandidates m).min' h)
  else none

/-- A selected scale is an actual candidate and an actual strict split. -/
theorem selectedBadScale_sound (m : Fin outerDepth) (rho : NNReal)
    (hselected : Q.selectedBadScale m = some rho) :
    rho ∈ Q.candidates m ∧
      IsBadScale A epsilon eta stage m rho := by
  unfold selectedBadScale at hselected
  split at hselected
  next hnonempty =>
    have heq : (Q.badCandidates m).min' hnonempty = rho := by
      exact Option.some.inj hselected
    rw [← heq]
    exact (Q.mem_badCandidates m _).1
      (Finset.min'_mem (Q.badCandidates m) hnonempty)
  next hnone =>
    exact (Option.some_ne_none rho hselected.symm).elim

/-- The selected bad scale is minimal among every bad candidate. -/
theorem selectedBadScale_minimal (m : Fin outerDepth) (rho : NNReal)
    (hselected : Q.selectedBadScale m = some rho) :
    forall sigma, sigma ∈ Q.candidates m ->
      IsBadScale A epsilon eta stage m sigma -> rho <= sigma := by
  unfold selectedBadScale at hselected
  split at hselected
  next hnonempty =>
    have heq : (Q.badCandidates m).min' hnonempty = rho := by
      exact Option.some.inj hselected
    intro sigma hsigma hbad
    rw [← heq]
    exact Finset.min'_le (Q.badCandidates m) sigma
      ((Q.mem_badCandidates m sigma).2 ⟨hsigma, hbad⟩)
  next hnone =>
    exact (Option.some_ne_none rho hselected.symm).elim

/-- Empty selection is equivalent to the finite bad-candidate set being
empty. -/
theorem selectedBadScale_eq_none_iff (m : Fin outerDepth) :
    Q.selectedBadScale m = none <-> Q.badCandidates m = ∅ := by
  by_cases hnonempty : (Q.badCandidates m).Nonempty
  · rw [selectedBadScale, dif_pos hnonempty]
    constructor
    · intro h
      exact (Option.some_ne_none _ h).elim
    · intro hempty
      exact ((Finset.nonempty_iff_ne_empty.mp hnonempty) hempty).elim
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [selectedBadScale, dif_neg hnonempty]
    exact iff_of_true rfl hempty

/-- If the finite selector returns no scale, no enumerated candidate is bad. -/
theorem not_bad_of_selectedBadScale_eq_none (m : Fin outerDepth)
    (hselected : Q.selectedBadScale m = none) :
    forall rho, rho ∈ Q.candidates m ->
      ¬ IsBadScale A epsilon eta stage m rho := by
  have hempty := (Q.selectedBadScale_eq_none_iff m).1 hselected
  intro rho hrho hbad
  have hmem : rho ∈ Q.badCandidates m :=
    (Q.mem_badCandidates m rho).2 ⟨hrho, hbad⟩
  rw [hempty] at hmem
  simp at hmem

/-- The genuinely analytic input is finite: every enumerated buffered scale
has the required non-strict lower inequality. -/
structure VerifiedCandidateLowerBounds where
  checked : forall m, ¬ S.IsLarge epsilon m ->
    forall rho, rho ∈ Q.candidates m ->
      S.IsBuffered epsilon m rho ->
        splitThreshold S eta stage m rho <= A.coarseValueAt m rho

namespace VerifiedCandidateLowerBounds

/-- Verified finite inequalities force the least-bad selector to return
`none`; no no-split proposition is stored in the certificate. -/
theorem selectedBadScale_eq_none
    (V : Q.VerifiedCandidateLowerBounds) (m : Fin outerDepth)
    (hlarge : ¬ S.IsLarge epsilon m) :
    Q.selectedBadScale m = none := by
  apply (Q.selectedBadScale_eq_none_iff m).2
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rho hrho
  have hspec := (Q.mem_badCandidates m rho).1 hrho
  exact (not_lt_of_ge (V.checked m hlarge rho hspec.1 hspec.2.1))
    hspec.2.2

/-- Finite selection plus threshold-free completeness produces the exact
terminal no-split proposition required by the actual dividing-scales run. -/
theorem terminal_noSplit
    (V : Q.VerifiedCandidateLowerBounds) : forall m,
    ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho < splitThreshold S eta stage m rho) := by
  intro m hlarge
  have hselected := V.selectedBadScale_eq_none Q m hlarge
  have hnotbad := Q.not_bad_of_selectedBadScale_eq_none m hselected
  rintro ⟨rho, hbuffered, hstrict⟩
  exact hnotbad rho (Q.buffered_complete m rho hbuffered)
    ⟨hbuffered, hstrict⟩

end VerifiedCandidateLowerBounds
end CandidateSearch

namespace BufferedChainFamily

variable {chainDepth adjacentDepth N : Nat}

/-- End-to-end actual run in which terminal no-split is synthesized by the
finite least-bad-scale search. -/
def toActualKatzTaoChainNoSplitRun_of_finiteSearch
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage eta)
    (adjacentExponent :
      AdjacentBufferedHierarchyFamily.ExponentBudgetData G stage eta)
    (search : CandidateSearch A epsilon eta stage)
    (verified : search.VerifiedCandidateLowerBounds) :
    KatzTaoChainNoSplitRun delta outerDepth chainDepth N epsilon eta S :=
  FamilyStickyScaleChainAdjacentUpperProducerV1.BufferedChainFamily.toActualKatzTaoChainNoSplitRun_of_bufferedExponentData A B G stage
    stage_pos stage_le eta_monotone eta_stage_le_epsilon globalExponent
    adjacentExponent (verified.terminal_noSplit search)

/-- The actual product, adjacent, and finite terminal producers close the
all-large versus dividing-witness dichotomy. -/
theorem allLarge_or_witness_of_finiteSearch
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (globalExponent :
      FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage eta)
    (adjacentExponent :
      AdjacentBufferedHierarchyFamily.ExponentBudgetData G stage eta)
    (search : CandidateSearch A epsilon eta stage)
    (verified : search.VerifiedCandidateLowerBounds) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) := by
  exact (toActualKatzTaoChainNoSplitRun_of_finiteSearch A B G stage stage_pos
    stage_le eta_monotone eta_stage_le_epsilon globalExponent
    adjacentExponent search verified).allLarge_or_witness

end BufferedChainFamily

#print axioms CandidateSearch.selectedBadScale_sound
#print axioms CandidateSearch.selectedBadScale_minimal
#print axioms CandidateSearch.selectedBadScale_eq_none_iff
#print axioms CandidateSearch.VerifiedCandidateLowerBounds.selectedBadScale_eq_none
#print axioms CandidateSearch.VerifiedCandidateLowerBounds.terminal_noSplit
#print axioms BufferedChainFamily.toActualKatzTaoChainNoSplitRun_of_finiteSearch
#print axioms BufferedChainFamily.allLarge_or_witness_of_finiteSearch

end
end FamilyStickyScaleChainTerminalFiniteSearchV1
