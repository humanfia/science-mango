import ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
import ArchonPhysics.NestedOscillatoryEnergyIdentity

/-!
# Shuffle linearization of branching FPUT oscillatory histories

This module upgrades linear ordered histories to genuine branching binary
Duhamel trees.  The central analytic input is the arbitrary-order Chen
shuffle identity: the product of two ordered oscillatory integrals is the sum
over all order-preserving interleavings of their phase lists.  Lists retain
multiplicity, so coincident numerical phases do not collapse distinct linear
extensions.

Using the existing `BinaryInteractionTree`, a node-labelled recursive
branching integral is then linearized exactly into its internal-node linear
extensions.  If every such extension satisfies the explicit cumulative gap
certificate from `FreeFPUTRegularArbitraryOrderOscillatoryHistory`, the tree
inherits a uniform bound with the exact linear-extension cardinality left
visible.  No kinetic equation or RPA assumption is used.
-/

namespace ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Topology
open scoped Interval

noncomputable section

/-! ## Arbitrary ordered-history shuffles -/

/-- All order-preserving interleavings of two phase lists.  This is a list,
not a finset: multiplicity records distinct linear extensions even when phase
values happen to coincide. -/
def orderedPhaseShuffles : List Real -> List Real -> List (List Real)
  | [], [] => [ [] ]
  | [], rightHead :: rightTail => [rightHead :: rightTail]
  | leftHead :: leftTail, [] => [leftHead :: leftTail]
  | leftHead :: leftTail, rightHead :: rightTail =>
      (orderedPhaseShuffles leftTail (rightHead :: rightTail)).map
          (List.cons leftHead) ++
        (orderedPhaseShuffles (leftHead :: leftTail) rightTail).map
          (List.cons rightHead)

@[simp] theorem orderedPhaseShuffles_nil_left (right : List Real) :
    orderedPhaseShuffles [] right = [right] := by
  cases right <;> simp [orderedPhaseShuffles]

@[simp] theorem orderedPhaseShuffles_nil_right
    (left : List Real) :
    orderedPhaseShuffles left [] = [left] := by
  cases left <;> simp [orderedPhaseShuffles]

/-- Every shuffle has the sum of the two input lengths. -/
theorem length_eq_add_of_mem_orderedPhaseShuffles
    {left right shuffled : List Real}
    (hmem : shuffled ∈ orderedPhaseShuffles left right) :
    shuffled.length = left.length + right.length := by
  cases left with
  | nil =>
      simp only [orderedPhaseShuffles_nil_left, List.mem_singleton] at hmem
      subst shuffled
      simp
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simp only [orderedPhaseShuffles_nil_right,
            List.mem_singleton] at hmem
          subst shuffled
          simp
      | cons rightHead rightTail =>
          simp only [orderedPhaseShuffles, List.mem_append,
            List.mem_map] at hmem
          rcases hmem with hleft | hright
          · rcases hleft with ⟨interleaving, hinterleaving, rfl⟩
            simp only [List.length_cons]
            rw [length_eq_add_of_mem_orderedPhaseShuffles hinterleaving]
            simp only [List.length_cons]
            omega
          · rcases hright with ⟨interleaving, hinterleaving, rfl⟩
            simp only [List.length_cons]
            rw [length_eq_add_of_mem_orderedPhaseShuffles hinterleaving]
            simp only [List.length_cons]
            omega
termination_by left.length + right.length
decreasing_by all_goals simp_all

/-- Sum of ordered oscillatory integrals over a family, retaining list
multiplicity. -/
def orderedOscillatoryIntegralFamilySum
    (histories : List (List Real)) (time : Real) : Complex :=
  (histories.map fun phases =>
    linearOrderedOscillatoryIntegral phases time).sum

@[simp] theorem orderedOscillatoryIntegralFamilySum_nil (time : Real) :
    orderedOscillatoryIntegralFamilySum [] time = 0 := rfl

@[simp] theorem orderedOscillatoryIntegralFamilySum_cons
    (phases : List Real) (histories : List (List Real)) (time : Real) :
    orderedOscillatoryIntegralFamilySum (phases :: histories) time =
      linearOrderedOscillatoryIntegral phases time +
        orderedOscillatoryIntegralFamilySum histories time := rfl

@[simp] theorem orderedOscillatoryIntegralFamilySum_append
    (left right : List (List Real)) (time : Real) :
    orderedOscillatoryIntegralFamilySum (left ++ right) time =
      orderedOscillatoryIntegralFamilySum left time +
        orderedOscillatoryIntegralFamilySum right time := by
  simp [orderedOscillatoryIntegralFamilySum]

theorem continuous_orderedOscillatoryIntegralFamilySum
    (histories : List (List Real)) :
    Continuous (orderedOscillatoryIntegralFamilySum histories) := by
  induction histories with
  | nil => exact continuous_const
  | cons phases histories ih =>
      exact (continuous_linearOrderedOscillatoryIntegral phases).add ih

/-- Prepending one outer phase to every history equals integrating that phase
against the family sum. -/
theorem orderedOscillatoryIntegralFamilySum_map_cons
    (delta : Real) (histories : List (List Real)) (time : Real) :
    orderedOscillatoryIntegralFamilySum
        (histories.map (List.cons delta)) time =
      ∫ t in (0 : Real)..time,
        Complex.exp ((Complex.I * delta) * t) *
          orderedOscillatoryIntegralFamilySum histories t := by
  induction histories generalizing time with
  | nil => simp [orderedOscillatoryIntegralFamilySum]
  | cons phases histories ih =>
      have hfirst : IntervalIntegrable (fun t : Real =>
          Complex.exp ((Complex.I * delta) * t) *
            linearOrderedOscillatoryIntegral phases t) volume 0 time :=
        ((by fun_prop : Continuous (fun t : Real =>
          Complex.exp ((Complex.I * delta) * t))).mul
            (continuous_linearOrderedOscillatoryIntegral phases))
          |>.intervalIntegrable (μ := volume) 0 time
      have hrest : IntervalIntegrable (fun t : Real =>
          Complex.exp ((Complex.I * delta) * t) *
            orderedOscillatoryIntegralFamilySum histories t) volume 0 time :=
        ((by fun_prop : Continuous (fun t : Real =>
          Complex.exp ((Complex.I * delta) * t))).mul
            (continuous_orderedOscillatoryIntegralFamilySum histories))
          |>.intervalIntegrable (μ := volume) 0 time
      simp only [List.map_cons,
        orderedOscillatoryIntegralFamilySum_cons,
        linearOrderedOscillatoryIntegral_cons]
      rw [ih]
      rw [← intervalIntegral.integral_add hfirst hrest]
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp
      ring

/-- Arbitrary-order Chen shuffle identity for the actual nested oscillatory
integrals. -/
theorem linearOrderedOscillatoryIntegral_mul_eq_shuffleSum
    (left right : List Real) (time : Real) :
    linearOrderedOscillatoryIntegral left time *
        linearOrderedOscillatoryIntegral right time =
      orderedOscillatoryIntegralFamilySum
        (orderedPhaseShuffles left right) time := by
  cases left with
  | nil =>
      simp [orderedOscillatoryIntegralFamilySum]
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simp [orderedOscillatoryIntegralFamilySum]
      | cons rightHead rightTail =>
          let leftFull := leftHead :: leftTail
          let rightFull := rightHead :: rightTail
          let leftPhase : Real -> Complex := fun t =>
            Complex.exp ((Complex.I * leftHead) * t)
          let rightPhase : Real -> Complex := fun t =>
            Complex.exp ((Complex.I * rightHead) * t)
          let derivative : Real -> Complex := fun t =>
            (leftPhase t *
                linearOrderedOscillatoryIntegral leftTail t) *
                linearOrderedOscillatoryIntegral rightFull t +
              linearOrderedOscillatoryIntegral leftFull t *
                (rightPhase t *
                  linearOrderedOscillatoryIntegral rightTail t)
          have hderiv (t : Real) :
              HasDerivAt (fun s : Real =>
                linearOrderedOscillatoryIntegral leftFull s *
                  linearOrderedOscillatoryIntegral rightFull s)
                (derivative t) t := by
            exact
              (hasDerivAt_linearOrderedOscillatoryIntegral_cons
                leftHead leftTail t).mul
              (hasDerivAt_linearOrderedOscillatoryIntegral_cons
                rightHead rightTail t)
          have hderivativeContinuous : Continuous derivative := by
            dsimp [derivative, leftPhase, rightPhase, leftFull, rightFull]
            exact (((by fun_prop : Continuous (fun t : Real =>
                Complex.exp ((Complex.I * leftHead) * t))).mul
                  (continuous_linearOrderedOscillatoryIntegral leftTail)).mul
                    (continuous_linearOrderedOscillatoryIntegral
                      (rightHead :: rightTail))).add
              ((continuous_linearOrderedOscillatoryIntegral
                  (leftHead :: leftTail)).mul
                ((by fun_prop : Continuous (fun t : Real =>
                    Complex.exp ((Complex.I * rightHead) * t))).mul
                  (continuous_linearOrderedOscillatoryIntegral rightTail)))
          have hproductIntegral :
              linearOrderedOscillatoryIntegral leftFull time *
                  linearOrderedOscillatoryIntegral rightFull time =
                ∫ t in (0 : Real)..time, derivative t := by
            have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun t _ht => hderiv t)
              (hderivativeContinuous.intervalIntegrable
                (μ := volume) 0 time)
            simpa [leftFull, rightFull,
              linearOrderedOscillatoryIntegral_cons_zero] using hFTC.symm
          let leftShuffles :=
            orderedPhaseShuffles leftTail rightFull
          let rightShuffles :=
            orderedPhaseShuffles leftFull rightTail
          have hintegrand : derivative = fun t : Real =>
              leftPhase t *
                  orderedOscillatoryIntegralFamilySum leftShuffles t +
                rightPhase t *
                  orderedOscillatoryIntegralFamilySum rightShuffles t := by
            funext t
            dsimp [derivative, leftPhase, rightPhase, leftShuffles,
              rightShuffles, leftFull, rightFull]
            rw [← linearOrderedOscillatoryIntegral_mul_eq_shuffleSum
                leftTail (rightHead :: rightTail) t,
              ← linearOrderedOscillatoryIntegral_mul_eq_shuffleSum
                (leftHead :: leftTail) rightTail t]
            rw [← linearOrderedOscillatoryIntegral_cons
                rightHead rightTail t,
              ← linearOrderedOscillatoryIntegral_cons
                leftHead leftTail t]
            ring
          have hleftIntegrable : IntervalIntegrable (fun t : Real =>
              leftPhase t *
                orderedOscillatoryIntegralFamilySum leftShuffles t)
              volume 0 time :=
            ((by fun_prop : Continuous leftPhase).mul
              (continuous_orderedOscillatoryIntegralFamilySum leftShuffles))
              |>.intervalIntegrable (μ := volume) 0 time
          have hrightIntegrable : IntervalIntegrable (fun t : Real =>
              rightPhase t *
                orderedOscillatoryIntegralFamilySum rightShuffles t)
              volume 0 time :=
            ((by fun_prop : Continuous rightPhase).mul
              (continuous_orderedOscillatoryIntegralFamilySum rightShuffles))
              |>.intervalIntegrable (μ := volume) 0 time
          calc
            linearOrderedOscillatoryIntegral (leftHead :: leftTail) time *
                linearOrderedOscillatoryIntegral
                  (rightHead :: rightTail) time =
                ∫ t in (0 : Real)..time, derivative t := by
              simpa [leftFull, rightFull] using hproductIntegral
            _ = ∫ t in (0 : Real)..time,
                leftPhase t *
                    orderedOscillatoryIntegralFamilySum leftShuffles t +
                  rightPhase t *
                    orderedOscillatoryIntegralFamilySum rightShuffles t := by
              rw [hintegrand]
            _ = (∫ t in (0 : Real)..time,
                    leftPhase t *
                      orderedOscillatoryIntegralFamilySum leftShuffles t) +
                  ∫ t in (0 : Real)..time,
                    rightPhase t *
                      orderedOscillatoryIntegralFamilySum rightShuffles t := by
              rw [intervalIntegral.integral_add
                hleftIntegrable hrightIntegrable]
            _ = orderedOscillatoryIntegralFamilySum
                    (leftShuffles.map (List.cons leftHead)) time +
                  orderedOscillatoryIntegralFamilySum
                    (rightShuffles.map (List.cons rightHead)) time := by
              rw [orderedOscillatoryIntegralFamilySum_map_cons,
                orderedOscillatoryIntegralFamilySum_map_cons]
            _ = orderedOscillatoryIntegralFamilySum
                  (orderedPhaseShuffles
                    (leftHead :: leftTail) (rightHead :: rightTail)) time := by
              dsimp [leftShuffles, rightShuffles, leftFull, rightFull]
              rw [orderedPhaseShuffles]
              simp
termination_by left.length + right.length
decreasing_by all_goals simp_all

/-! ## Shuffling whole families -/

/-- All pairwise shuffles of two families, again retaining multiplicity. -/
def shufflePhaseFamilies
    (left right : List (List Real)) : List (List Real) :=
  left.flatMap fun leftHistory =>
    right.flatMap fun rightHistory =>
      orderedPhaseShuffles leftHistory rightHistory

private theorem orderedOscillatoryIntegralFamilySum_flatMap_singleShuffle
    (leftHistory : List Real) (rightFamily : List (List Real))
    (time : Real) :
    orderedOscillatoryIntegralFamilySum
        (rightFamily.flatMap fun rightHistory =>
          orderedPhaseShuffles leftHistory rightHistory) time =
      linearOrderedOscillatoryIntegral leftHistory time *
        orderedOscillatoryIntegralFamilySum rightFamily time := by
  induction rightFamily with
  | nil => simp [orderedOscillatoryIntegralFamilySum]
  | cons rightHistory rightFamily ih =>
      simp only [List.flatMap_cons,
        orderedOscillatoryIntegralFamilySum_append,
        orderedOscillatoryIntegralFamilySum_cons]
      rw [← linearOrderedOscillatoryIntegral_mul_eq_shuffleSum, ih]
      ring

/-- Bilinearity plus the single-pair shuffle theorem gives the shuffle
identity for arbitrary finite families. -/
theorem orderedOscillatoryIntegralFamilySum_shufflePhaseFamilies
    (left right : List (List Real)) (time : Real) :
    orderedOscillatoryIntegralFamilySum
        (shufflePhaseFamilies left right) time =
      orderedOscillatoryIntegralFamilySum left time *
        orderedOscillatoryIntegralFamilySum right time := by
  induction left with
  | nil => simp [shufflePhaseFamilies, orderedOscillatoryIntegralFamilySum]
  | cons leftHistory leftFamily ih =>
      unfold shufflePhaseFamilies
      simp only [List.flatMap_cons,
        orderedOscillatoryIntegralFamilySum_append,
        orderedOscillatoryIntegralFamilySum_cons]
      rw [orderedOscillatoryIntegralFamilySum_flatMap_singleShuffle,
        ← shufflePhaseFamilies, ih]
      ring

/-! ## Genuine branching binary-tree Duhamel integrals -/

/-- A real phase label at every internal node of an existing
`BinaryInteractionTree`. -/
def BinaryInteractionTreePhaseAssignment :
    BinaryInteractionTree -> Type
  | .leaf => PUnit
  | .node left right =>
      Real × (BinaryInteractionTreePhaseAssignment left ×
        BinaryInteractionTreePhaseAssignment right)

/-- Genuine recursively branching oscillatory Duhamel integral:
`I_node(T) = integral exp(i delta_node t) I_left(t) I_right(t) dt`. -/
def branchingOscillatoryDuhamelIntegral :
    (tree : BinaryInteractionTree) ->
      BinaryInteractionTreePhaseAssignment tree -> Real -> Complex
  | .leaf, _assignment, _time => 1
  | .node left right, assignment, time =>
      ∫ t in (0 : Real)..time,
        Complex.exp ((Complex.I * assignment.1) * t) *
          branchingOscillatoryDuhamelIntegral left assignment.2.1 t *
          branchingOscillatoryDuhamelIntegral right assignment.2.2 t

@[simp] theorem branchingOscillatoryDuhamelIntegral_leaf
    (assignment : BinaryInteractionTreePhaseAssignment .leaf)
    (time : Real) :
    branchingOscillatoryDuhamelIntegral .leaf assignment time = 1 := rfl

@[simp] theorem branchingOscillatoryDuhamelIntegral_node
    (left right : BinaryInteractionTree)
    (assignment :
      BinaryInteractionTreePhaseAssignment (.node left right))
    (time : Real) :
    branchingOscillatoryDuhamelIntegral (.node left right) assignment time =
      ∫ t in (0 : Real)..time,
        Complex.exp ((Complex.I * assignment.1) * t) *
          branchingOscillatoryDuhamelIntegral left assignment.2.1 t *
          branchingOscillatoryDuhamelIntegral right assignment.2.2 t := rfl

theorem continuous_branchingOscillatoryDuhamelIntegral
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    Continuous (branchingOscillatoryDuhamelIntegral tree assignment) := by
  induction tree with
  | leaf => exact continuous_const
  | node left right hleft hright =>
      change Continuous (fun endpoint : Real =>
        ∫ t in (0 : Real)..endpoint,
          Complex.exp ((Complex.I * assignment.1) * t) *
            branchingOscillatoryDuhamelIntegral left assignment.2.1 t *
            branchingOscillatoryDuhamelIntegral right assignment.2.2 t)
      apply (intervalIntegral.differentiable_integral_of_continuous ?_).continuous
      exact ((by fun_prop : Continuous (fun t : Real =>
          Complex.exp ((Complex.I * assignment.1) * t))).mul
            (hleft assignment.2.1)).mul
        (hright assignment.2.2)

/-- Linear extensions of the internal-node tree order.  The root is outermost
and therefore first; the two child extensions are freely shuffled. -/
def branchingPhaseLinearExtensions :
    (tree : BinaryInteractionTree) ->
      BinaryInteractionTreePhaseAssignment tree -> List (List Real)
  | .leaf, _assignment => [ [] ]
  | .node left right, assignment =>
      (shufflePhaseFamilies
        (branchingPhaseLinearExtensions left assignment.2.1)
        (branchingPhaseLinearExtensions right assignment.2.2)).map
          (List.cons assignment.1)

/-- Every branching linear extension contains exactly one phase per internal
node. -/
theorem length_eq_order_of_mem_branchingPhaseLinearExtensions
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree)
    {phases : List Real}
    (hmem : phases ∈ branchingPhaseLinearExtensions tree assignment) :
    phases.length = tree.order := by
  induction tree generalizing phases with
  | leaf =>
      simp [branchingPhaseLinearExtensions] at hmem
      subst phases
      rfl
  | node left right hleft hright =>
      simp only [branchingPhaseLinearExtensions, List.mem_map] at hmem
      rcases hmem with ⟨childShuffle, hchildShuffle, rfl⟩
      unfold shufflePhaseFamilies at hchildShuffle
      simp only [List.mem_flatMap] at hchildShuffle
      rcases hchildShuffle with
        ⟨leftPhases, hleftMem, rightPhases, hrightMem, hshuffleMem⟩
      simp only [List.length_cons, BinaryInteractionTree.order]
      rw [length_eq_add_of_mem_orderedPhaseShuffles hshuffleMem,
        hleft assignment.2.1 hleftMem,
        hright assignment.2.2 hrightMem]

/-- Exact Chen/shuffle linearization of every finite branching binary
Duhamel tree. -/
theorem branchingOscillatoryDuhamelIntegral_eq_linearExtensionSum
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree)
    (time : Real) :
    branchingOscillatoryDuhamelIntegral tree assignment time =
      orderedOscillatoryIntegralFamilySum
        (branchingPhaseLinearExtensions tree assignment) time := by
  induction tree generalizing time with
  | leaf => simp [branchingPhaseLinearExtensions]
  | node left right hleft hright =>
      let leftExtensions :=
        branchingPhaseLinearExtensions left assignment.2.1
      let rightExtensions :=
        branchingPhaseLinearExtensions right assignment.2.2
      let childShuffles :=
        shufflePhaseFamilies leftExtensions rightExtensions
      rw [branchingOscillatoryDuhamelIntegral_node]
      calc
        (∫ t in (0 : Real)..time,
            Complex.exp ((Complex.I * assignment.1) * t) *
                branchingOscillatoryDuhamelIntegral left assignment.2.1 t *
              branchingOscillatoryDuhamelIntegral right assignment.2.2 t) =
            ∫ t in (0 : Real)..time,
              Complex.exp ((Complex.I * assignment.1) * t) *
                orderedOscillatoryIntegralFamilySum leftExtensions t *
                orderedOscillatoryIntegralFamilySum rightExtensions t := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp
          rw [hleft assignment.2.1 t, hright assignment.2.2 t]
        _ = ∫ t in (0 : Real)..time,
              Complex.exp ((Complex.I * assignment.1) * t) *
                orderedOscillatoryIntegralFamilySum childShuffles t := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp [childShuffles]
          rw [orderedOscillatoryIntegralFamilySum_shufflePhaseFamilies]
          ring
        _ = orderedOscillatoryIntegralFamilySum
              (childShuffles.map (List.cons assignment.1)) time := by
          rw [orderedOscillatoryIntegralFamilySum_map_cons]
        _ = orderedOscillatoryIntegralFamilySum
              (branchingPhaseLinearExtensions
                (.node left right) assignment) time := by
          rfl

/-! ## Fully nonresonant branching bound -/

/-- Every internal-node linear extension of the branching history obeys the
same explicit cumulative-gap certificate. -/
def FullyNonresonantBranchingHistory
    (gamma : Real) (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) : Prop :=
  forall phases,
    phases ∈ branchingPhaseLinearExtensions tree assignment ->
      FullyNonresonantOrderedHistory gamma phases

/-- Norm of a finite ordered-integral family sum, with list length retaining
the exact multiplicity. -/
theorem norm_orderedOscillatoryIntegralFamilySum_le_length_mul
    (histories : List (List Real)) (time B : Real)
    (hbound : forall phases,
      phases ∈ histories ->
        ‖linearOrderedOscillatoryIntegral phases time‖ <= B) :
    ‖orderedOscillatoryIntegralFamilySum histories time‖ <=
      (histories.length : Real) * B := by
  induction histories with
  | nil => simp
  | cons phases histories ih =>
      rw [orderedOscillatoryIntegralFamilySum_cons]
      calc
        ‖linearOrderedOscillatoryIntegral phases time +
            orderedOscillatoryIntegralFamilySum histories time‖ <=
            ‖linearOrderedOscillatoryIntegral phases time‖ +
              ‖orderedOscillatoryIntegralFamilySum histories time‖ :=
          norm_add_le _ _
        _ <= B + (histories.length : Real) * B := by
          exact add_le_add
            (hbound phases (by simp))
            (ih (fun history hhistory =>
              hbound history (by simp [hhistory])))
        _ = ((phases :: histories).length : Real) * B := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Full branching arbitrary-order bound.  The exact number of linear
extensions is deliberately visible: no false uniform exponential estimate
for this combinatorial factor is inserted. -/
theorem norm_branchingOscillatoryDuhamelIntegral_le_linearExtensionCard
    {gamma : Real} (hgamma : 0 < gamma)
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree)
    (hregular : FullyNonresonantBranchingHistory gamma tree assignment)
    (time : Real) :
    ‖branchingOscillatoryDuhamelIntegral tree assignment time‖ <=
      ((branchingPhaseLinearExtensions tree assignment).length : Real) *
        (2 / gamma) ^ tree.order := by
  rw [branchingOscillatoryDuhamelIntegral_eq_linearExtensionSum]
  apply norm_orderedOscillatoryIntegralFamilySum_le_length_mul
  intro phases hphases
  have hbound := norm_linearOrderedOscillatoryIntegral_le_resolvent
    hgamma (hregular phases hphases) time
  rw [length_eq_order_of_mem_branchingPhaseLinearExtensions
    tree assignment hphases] at hbound
  exact hbound

/-! ## Fixed-root FPUT branching-history handoff -/

/-- Existing fixed-root raw histories, now carrying a genuine phase label at
every internal node rather than an externally supplied linear phase list. -/
def fixedRootBranchingOscillatoryHistoryCoefficient
    (N : Nat) [NeZero N] (rootMomentum : Lattice.Site N)
    (amplitude :
      (r : Nat) ->
        FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
          N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history :
          FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
            N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (time : Real) (r : Nat)
    (history :
      FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
        N r rootMomentum) : Complex :=
  amplitude r history *
    branchingOscillatoryDuhamelIntegral history.1.1
      (phaseAssignment r history) time

/-- Per-history full-branching estimate, retaining its exact linear-extension
count. -/
theorem norm_fixedRootBranchingOscillatoryHistoryCoefficient_le
    (N : Nat) [NeZero N] (rootMomentum : Lattice.Site N)
    (amplitude :
      (r : Nat) ->
        FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
          N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history :
          FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
            N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma)
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (hregular : forall r history,
      FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history))
    (time : Real) (r : Nat)
    (history :
      FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
        N r rootMomentum) :
    ‖fixedRootBranchingOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseAssignment time r history‖ <=
      A * rho ^ r *
        ((branchingPhaseLinearExtensions history.1.1
          (phaseAssignment r history)).length : Real) *
        (2 / gamma) ^ r := by
  have hbranch :=
    norm_branchingOscillatoryDuhamelIntegral_le_linearExtensionCard
      hgamma history.1.1 (phaseAssignment r history)
        (hregular r history) time
  rw [history.1.2] at hbranch
  unfold fixedRootBranchingOscillatoryHistoryCoefficient
  rw [norm_mul]
  calc
    ‖amplitude r history‖ *
        ‖branchingOscillatoryDuhamelIntegral history.1.1
          (phaseAssignment r history) time‖ <=
        (A * rho ^ r) *
          (((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) *
              (2 / gamma) ^ r) := by
      exact mul_le_mul (hamplitude r history) hbranch
        (norm_nonneg _)
        (mul_nonneg hA (pow_nonneg hrho r))
    _ = A * rho ^ r *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) *
          (2 / gamma) ^ r := by ring

/-- If the amplitude pays for the exact linear-extension multiplicity, the
full branching coefficient recovers a geometric single-history estimate.
This is the precise additional analytic input needed before reusing the
Catalan tail theorem. -/
theorem norm_fixedRootBranchingOscillatoryHistoryCoefficient_le_geometric
    (N : Nat) [NeZero N] (rootMomentum : Lattice.Site N)
    (amplitude :
      (r : Nat) ->
        FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
          N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history :
          FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
            N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma : Real} (_hA : 0 <= A) (_hrho : 0 <= rho)
    (hgamma : 0 < gamma)
    (hamplitudeWeighted : forall r history,
      ‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) <=
        A * rho ^ r)
    (hregular : forall r history,
      FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history))
    (time : Real) (r : Nat)
    (history :
      FreeFPUTBinaryTreeCatalanMomentumCounting.FixedRootRawHistoryIndex
        N r rootMomentum) :
    ‖fixedRootBranchingOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseAssignment time r history‖ <=
      A * (2 * rho / gamma) ^ r := by
  have hbranch :=
    norm_branchingOscillatoryDuhamelIntegral_le_linearExtensionCard
      hgamma history.1.1 (phaseAssignment r history)
        (hregular r history) time
  rw [history.1.2] at hbranch
  unfold fixedRootBranchingOscillatoryHistoryCoefficient
  rw [norm_mul]
  calc
    ‖amplitude r history‖ *
        ‖branchingOscillatoryDuhamelIntegral history.1.1
          (phaseAssignment r history) time‖ <=
        ‖amplitude r history‖ *
          (((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) *
              (2 / gamma) ^ r) :=
      mul_le_mul_of_nonneg_left hbranch (norm_nonneg _)
    _ = (‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real)) *
          (2 / gamma) ^ r := by ring
    _ <= (A * rho ^ r) * (2 / gamma) ^ r :=
      mul_le_mul_of_nonneg_right (hamplitudeWeighted r history)
        (pow_nonneg (by positivity) r)
    _ = A * (2 * rho / gamma) ^ r := by
      rw [show 2 * rho / gamma = rho * (2 / gamma) by ring, mul_pow]
      ring

/-- Full-branching sufficient condition for the `q/(16N)` single-history
premise of the arbitrary-order Catalan majorant. -/
theorem norm_fixedRootBranchingOscillatoryHistoryCoefficient_le_catalanScale
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (_hq : 0 <= q)
    (hratio : 2 * rho / gamma <= q / (16 * (N : Real)))
    (hamplitudeWeighted : forall r history,
      ‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) <=
        A * rho ^ r)
    (hregular : forall r history,
      FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history))
    (time : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    ‖fixedRootBranchingOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseAssignment time r history‖ <=
      A * singleHistoryCatalanScale N q r := by
  have hratio0 : 0 <= 2 * rho / gamma := by positivity
  calc
    ‖fixedRootBranchingOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseAssignment time r history‖ <=
        A * (2 * rho / gamma) ^ r :=
      norm_fixedRootBranchingOscillatoryHistoryCoefficient_le_geometric
        N rootMomentum amplitude phaseAssignment hA hrho hgamma
          hamplitudeWeighted hregular time r history
    _ <= A * (q / (16 * (N : Real))) ^ r := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hratio0 hratio r) hA
    _ = A * singleHistoryCatalanScale N q r := rfl

/-- The complete fixed-root branching series inherits the explicit Catalan
order and tail bounds once the exact extension-weighted amplitude condition
and the cumulative-gap condition have been verified. -/
theorem fixedRootBranchingOscillatoryHistory_tail_certificate
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (hq0 : 0 <= q) (hq1 : q < 1)
    (hratio : 2 * rho / gamma <= q / (16 * (N : Real)))
    (hamplitudeWeighted : forall r history,
      ‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) <=
        A * rho ^ r)
    (hregular : forall r history,
      FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history))
    (time : Real) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) r‖ <=
        A * q ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) R‖ <=
        A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) R‖)
      atTop (nhds 0) := by
  have hsingle : forall r history,
      ‖fixedRootBranchingOscillatoryHistoryCoefficient
          N rootMomentum amplitude phaseAssignment time r history‖ <=
        A * singleHistoryCatalanScale N q r := by
    intro r history
    exact
      norm_fixedRootBranchingOscillatoryHistoryCoefficient_le_catalanScale
        N rootMomentum amplitude phaseAssignment hA hrho hgamma hq0
          hratio hamplitudeWeighted hregular time r history
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact norm_fixedRootRawHistoryOrderSum_le_geometric
      N rootMomentum _ hA hq0 hsingle r
  · intro R
    exact norm_fixedRootRawHistoryTail_le_geometric
      N rootMomentum _ hA hq0 hq1 hsingle R
  · exact norm_fixedRootRawHistoryTail_tendsto_zero
      N rootMomentum _ hA hq0 hq1 hsingle

end


end ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
