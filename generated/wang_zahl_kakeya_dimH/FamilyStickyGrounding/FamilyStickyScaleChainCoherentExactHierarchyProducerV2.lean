import FamilyStickyGrounding.FamilyStickyScaleCoverAdjacentStepBridgeV2
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentIntervalProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainActualDividingRunV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCoherentExactHierarchyProducerV2

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2

noncomputable section

/-!
# Exact zero-buffer hierarchies from coherent Sticky covers

A supplied finite chain below is genuinely finite: its radii are indexed by
`Fin (depth + 1)`.  The hierarchy API asks for families at every natural
level, even though only `0, ..., depth` are certified.  We therefore clamp
out-of-range natural levels to the final finite level.  No family, radius, or
cardinality is supplied independently of the coherent cover.

Every certified adjacent step is the exact `.partition` bridge applied to
`CoherentStickyMultiscaleCover.intervalScaleCover`.  Consequently its raw
cost is zero and recursive buffering vanishes.  The only additional
structural input is nonemptiness of the original refined fine family; this
forces every chosen coarse family to be nonempty through the actual parent
map already stored in each Sticky cover.
-/

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A supplied finite monotone chain of radii, explicitly bounded in the
scale interval on which a coherent Sticky cover is defined. -/
structure BoundedMonotoneRadiusChain (delta : NNReal) (depth : Nat) where
  radius : Fin (depth + 1) -> NNReal
  monotone_radius : Monotone radius
  delta_le_radius : forall j, delta <= radius j
  radius_le_one : forall j, radius j <= 1

namespace BoundedMonotoneRadiusChain

variable {depth : Nat}

/-- Clamp the all-natural hierarchy level to the last supplied finite level. -/
def level (_R : BoundedMonotoneRadiusChain delta depth) (l : Nat) :
    Fin (depth + 1) :=
  ⟨min l depth, Nat.lt_succ_of_le (Nat.min_le_right l depth)⟩

@[simp] theorem level_val (R : BoundedMonotoneRadiusChain delta depth)
    (l : Nat) : (R.level l).1 = min l depth := by
  rfl

theorem level_mono (R : BoundedMonotoneRadiusChain delta depth) :
    Monotone R.level := by
  intro a b hab
  change min a depth <= min b depth
  omega

/-- The clamped all-natural nominal radius used by the hierarchy. -/
def nominalRadius (R : BoundedMonotoneRadiusChain delta depth)
    (l : Nat) : NNReal :=
  R.radius (R.level l)

theorem nominalRadius_mono (R : BoundedMonotoneRadiusChain delta depth) :
    Monotone R.nominalRadius := by
  intro a b hab
  exact R.monotone_radius (R.level_mono hab)

theorem delta_le_nominalRadius
    (R : BoundedMonotoneRadiusChain delta depth) (l : Nat) :
    delta <= R.nominalRadius l :=
  R.delta_le_radius (R.level l)

theorem nominalRadius_le_one
    (R : BoundedMonotoneRadiusChain delta depth) (l : Nat) :
    R.nominalRadius l <= 1 :=
  R.radius_le_one (R.level l)

theorem nominalRadius_step_le
    (R : BoundedMonotoneRadiusChain delta depth)
    (l : Nat) (_hl : l < depth) :
    R.nominalRadius l <= R.nominalRadius (l + 1) :=
  R.nominalRadius_mono (Nat.le_succ l)

/-- The actual Sticky cover selected by `C` at a clamped chain level. -/
def selectedCover
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine) (l : Nat) :
    StickyScaleCover fine (R.nominalRadius l) :=
  C.base.cover (R.nominalRadius l) (R.delta_le_nominalRadius l)
    (R.nominalRadius_le_one l)

/-- The level cardinality is not independent data: it is the actual coarse
cardinality chosen by the coherent cover. -/
def card (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine) (l : Nat) : Nat :=
  (R.selectedCover C l).coarseCard

/-- The raw hierarchy family is exactly the coherent cover's selected coarse
family at this radius. -/
def family (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine) (l : Nat) :
    UniformTubeFamily (R.nominalRadius l) (Fin (R.card C l)) :=
  (R.selectedCover C l).coarse

/-- One nonempty original refined occurrence produces an active parent in
every selected cover. -/
theorem selectedCover_activeCoarse_nonempty
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty) (l : Nat) :
    (R.selectedCover C l).activeCoarse.Nonempty := by
  let U := R.selectedCover C l
  have hactiveFine : U.activeFine.Nonempty := by
    rw [U.activeFine_eq_refined]
    exact hfine
  obtain ⟨i, hi⟩ := hactiveFine
  exact ⟨U.parent i, U.parent_mem i hi⟩

/-- The literal coherent cover from level `l` to level `l+1`. -/
def intervalCover
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (l : Nat) (hl : l < depth) :
    StickyScaleCover (R.family C l) (R.nominalRadius (l + 1)) :=
  C.intervalScaleCover (R.nominalRadius l) (R.nominalRadius (l + 1))
    (R.delta_le_nominalRadius l) (R.nominalRadius_step_le l hl)
    (R.nominalRadius_le_one (l + 1))

theorem intervalCover_activeCoarse_nonempty
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    (R.intervalCover C l hl).activeCoarse.Nonempty := by
  exact R.selectedCover_activeCoarse_nonempty C hfine (l + 1)

/-- The actual exact partition underlying one coherent interval. -/
def exactPartition
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    CoarseTubePartition (R.family C l) (R.family C (l + 1)) :=
  toCoarseTubePartition (R.intervalCover C l hl)
    (R.nominalRadius_step_le l hl)
    (R.intervalCover_activeCoarse_nonempty C hfine l hl)

/-- The repository's exact adjacent-step constructor applied to the coherent
interval cover. -/
def exactStep
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    AdjacentTubeStep (R.family C l) (R.family C (l + 1)) :=
  .partition (R.exactPartition C hfine l hl)

/-- The genuine coherent exact hierarchy.  Its all-natural tail is the
clamped final supplied family and is not used by any certified step. -/
def toHierarchy
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty) :
    MultiscaleTubeHierarchy depth R.nominalRadius
      (fun l => Fin (R.card C l)) where
  family := R.family C
  step := R.exactStep C hfine

@[simp] theorem toHierarchy_family
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty) (l : Nat) :
    (R.toHierarchy C hfine).family l = R.family C l := by
  rfl

@[simp] theorem toHierarchy_step
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    (R.toHierarchy C hfine).step l hl = R.exactStep C hfine l hl := by
  rfl

theorem toHierarchy_step_eq_interval_partition
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    (R.toHierarchy C hfine).step l hl =
      .partition (R.exactPartition C hfine l hl) := by
  rfl

/-- The same fact stated directly through the public Sticky-cover bridge. -/
theorem toHierarchy_step_eq_coherentBridge
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    (R.toHierarchy C hfine).step l hl =
      toAdjacentTubeStep (R.intervalCover C l hl)
        (R.nominalRadius_step_le l hl)
        (R.intervalCover_activeCoarse_nonempty C hfine l hl) := by
  rfl

@[simp] theorem toHierarchy_step_rawCost
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    ((R.toHierarchy C hfine).step l hl).rawCost = 0 := by
  rfl

@[simp] theorem toHierarchy_step_branchingFactor
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    ((R.toHierarchy C hfine).step l hl).combinatorics.branchingFactor =
      (R.intervalCover C l hl).activeFine.card := by
  change (R.intervalCover C l hl).activeFine.card * 1 =
    (R.intervalCover C l hl).activeFine.card
  exact Nat.mul_one _

/-- Every accumulated raw cost vanishes, including on the clamped tail. -/
@[simp] theorem toHierarchy_accumulatedBuffer
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty) (l : Nat) :
    (R.toHierarchy C hfine).accumulatedBuffer l = 0 := by
  induction l with
  | zero => rfl
  | succ l ih =>
      simp only [MultiscaleTubeHierarchy.accumulatedBuffer]
      split_ifs with hl
      · rw [toHierarchy_step_rawCost R C hfine l hl, ih]
        exact zero_add 0
      · exact ih

/-- Exact steps have no buffer inflation: every effective radius is the
supplied nominal radius. -/
@[simp] theorem toHierarchy_effectiveRadius
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty) (l : Nat) :
    (R.toHierarchy C hfine).effectiveRadius l = R.nominalRadius l := by
  simp [MultiscaleTubeHierarchy.effectiveRadius]

/-- The effective partition retains the coherent cover's parent map. -/
@[simp] theorem effectivePartition_parent
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) (i : Fin (R.card C l)) :
    ((R.toHierarchy C hfine).effectivePartition l hl).index.parent i =
      (R.intervalCover C l hl).parent i := by
  rfl

/-- The effective partition also retains every literal coherent fiber. -/
@[simp] theorem effectivePartition_fiber
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) (k : Fin (R.card C (l + 1))) :
    ((R.toHierarchy C hfine).effectivePartition l hl).fiber k =
      (R.intervalCover C l hl).fiber k := by
  rfl

/-- Normalize the exact source partition using the existing repository
converter. -/
def normalizedSourceCover
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    StickyScaleCover (R.family C l) (R.nominalRadius (l + 1)) :=
  normalizedRoundTrip (R.intervalCover C l hl)
    (R.nominalRadius_step_le l hl)
    (R.intervalCover_activeCoarse_nonempty C hfine l hl)

/-- The normalized exact partition is the supplied coherent interval cover,
as a full structure rather than only up to bounds. -/
@[simp] theorem normalizedSourceCover_eq_intervalCover
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    R.normalizedSourceCover C hfine l hl = R.intervalCover C l hl := by
  exact normalizedRoundTrip_eq (R.intervalCover C l hl)
    (R.nominalRadius_step_le l hl)
    (R.intervalCover_activeCoarse_nonempty C hfine l hl)

@[simp] theorem normalizedSourceCover_fiberDeltaMax
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    fiberDeltaMax (R.normalizedSourceCover C hfine l hl) =
      fiberDeltaMax (R.intervalCover C l hl) := by
  rw [R.normalizedSourceCover_eq_intervalCover C hfine l hl]

@[simp] theorem normalizedSourceCover_coarseDeltaMax
    (R : BoundedMonotoneRadiusChain delta depth)
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (l : Nat) (hl : l < depth) :
    coarseDeltaMax (R.normalizedSourceCover C hfine l hl) =
      coarseDeltaMax (R.intervalCover C l hl) := by
  rw [R.normalizedSourceCover_eq_intervalCover C hfine l hl]

/-! ## Canonical one-step chain on a dividing-scale interval -/

/-- The canonical depth-one chain on one adjacent dividing-scale interval.
Level zero is the lower child radius `tau`; level one is the upper parent
radius `theta`.  There are no chosen intermediate scales. -/
def ofAdjacentInterval {outerDepth : Nat}
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (m : Fin outerDepth) : BoundedMonotoneRadiusChain delta 1 where
  radius := fun j => if j = 0 then S.tau m else S.theta m
  monotone_radius := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [S.tau_le_theta m]
  delta_le_radius := by
    intro j
    fin_cases j
    · simpa using S.delta_le_tau m
    · simpa using (S.delta_le_tau m).trans (S.tau_le_theta m)
  radius_le_one := by
    intro j
    fin_cases j
    · simpa using (S.tau_le_theta m).trans (S.theta_le_one m)
    · simpa using S.theta_le_one m

@[simp] theorem ofAdjacentInterval_radius_zero {outerDepth : Nat}
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (m : Fin outerDepth) :
    (ofAdjacentInterval S m).radius 0 = S.tau m := by
  rfl

@[simp] theorem ofAdjacentInterval_radius_one {outerDepth : Nat}
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (m : Fin outerDepth) :
    (ofAdjacentInterval S m).radius 1 = S.theta m := by
  rfl

@[simp] theorem ofAdjacentInterval_nominalRadius_zero {outerDepth : Nat}
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (m : Fin outerDepth) :
    (ofAdjacentInterval S m).nominalRadius 0 = S.tau m := by
  rfl

@[simp] theorem ofAdjacentInterval_nominalRadius_one {outerDepth : Nat}
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (m : Fin outerDepth) :
    (ofAdjacentInterval S m).nominalRadius 1 = S.theta m := by
  rfl

theorem ofAdjacentInterval_intervalCover_zero {outerDepth : Nat}
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (C : CoherentStickyMultiscaleCover fine) (m : Fin outerDepth) :
    (ofAdjacentInterval S m).intervalCover C 0 (by omega) =
      C.intervalScaleCover (S.tau m) (S.theta m)
        (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m) := by
  rfl

end BoundedMonotoneRadiusChain

/-!
The following bundle matches the radius, cardinality, and hierarchy fields of
`BufferedChainFamily` for every outer interval.  A full conversion requires
exactly the remaining `BufferedTestBodyChain` data; that analytic measure
bundle cannot be produced from parent maps and tube containment alone.
-/

/-- A finite outer family of coherent zero-buffer hierarchies. -/
structure CoherentExactHierarchyFamily
    (C : CoherentStickyMultiscaleCover fine)
    (outerDepth chainDepth : Nat) where
  fine_refined_nonempty : fine.refinement.refined.Nonempty
  chain : Fin outerDepth -> BoundedMonotoneRadiusChain delta chainDepth

namespace CoherentExactHierarchyFamily

variable {outerDepth chainDepth : Nat}
  {C : CoherentStickyMultiscaleCover fine}

def nominalRadius (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (m : Fin outerDepth) : Nat -> NNReal :=
  (F.chain m).nominalRadius

def card (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (m : Fin outerDepth) : Nat -> Nat :=
  fun l => (F.chain m).card C l

def hierarchy (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (m : Fin outerDepth) :
    MultiscaleTubeHierarchy chainDepth (F.nominalRadius m)
      (fun l => Fin (F.card m l)) :=
  (F.chain m).toHierarchy C F.fine_refined_nonempty

/-- Canonical outer family: the hierarchy for interval `m` is the single
exact coherent step `tau_m -> theta_m`. -/
def ofFiniteScaleSequence
    (C : CoherentStickyMultiscaleCover fine)
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (hfine : fine.refinement.refined.Nonempty) :
    CoherentExactHierarchyFamily C outerDepth 1 where
  fine_refined_nonempty := hfine
  chain := fun m => BoundedMonotoneRadiusChain.ofAdjacentInterval S m

@[simp] theorem ofFiniteScaleSequence_nominalRadius_zero
    (C : CoherentStickyMultiscaleCover fine)
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (hfine : fine.refinement.refined.Nonempty) (m : Fin outerDepth) :
    (ofFiniteScaleSequence C S hfine).nominalRadius m 0 = S.tau m := by
  rfl

@[simp] theorem ofFiniteScaleSequence_nominalRadius_one
    (C : CoherentStickyMultiscaleCover fine)
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (hfine : fine.refinement.refined.Nonempty) (m : Fin outerDepth) :
    (ofFiniteScaleSequence C S hfine).nominalRadius m 1 = S.theta m := by
  rfl

@[simp] theorem ofFiniteScaleSequence_effectiveRadius_zero
    (C : CoherentStickyMultiscaleCover fine)
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (hfine : fine.refinement.refined.Nonempty) (m : Fin outerDepth) :
    ((ofFiniteScaleSequence C S hfine).hierarchy m).effectiveRadius 0 =
      S.tau m := by
  change
    ((BoundedMonotoneRadiusChain.ofAdjacentInterval S m).toHierarchy
      C hfine).effectiveRadius 0 = S.tau m
  rw [BoundedMonotoneRadiusChain.toHierarchy_effectiveRadius]
  rfl

@[simp] theorem ofFiniteScaleSequence_effectiveRadius_one
    (C : CoherentStickyMultiscaleCover fine)
    (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
      delta outerDepth)
    (hfine : fine.refinement.refined.Nonempty) (m : Fin outerDepth) :
    ((ofFiniteScaleSequence C S hfine).hierarchy m).effectiveRadius 1 =
      S.theta m := by
  change
    ((BoundedMonotoneRadiusChain.ofAdjacentInterval S m).toHierarchy
      C hfine).effectiveRadius 1 = S.theta m
  rw [BoundedMonotoneRadiusChain.toHierarchy_effectiveRadius]
  rfl

/-- Once the genuinely additional test-body and measure certificates are
supplied, the remaining `BufferedChainFamily` packaging is automatic. -/
def toBufferedChainFamily
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (datum : (m : Fin outerDepth) ->
      FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain
        (F.hierarchy m)) :
    FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth where
  nominalRadius := F.nominalRadius
  card := F.card
  hierarchy := F.hierarchy
  datum := datum

end CoherentExactHierarchyFamily

#print axioms BoundedMonotoneRadiusChain.toHierarchy
#print axioms BoundedMonotoneRadiusChain.toHierarchy_step_eq_interval_partition
#print axioms BoundedMonotoneRadiusChain.toHierarchy_step_eq_coherentBridge
#print axioms BoundedMonotoneRadiusChain.toHierarchy_step_branchingFactor
#print axioms BoundedMonotoneRadiusChain.toHierarchy_accumulatedBuffer
#print axioms BoundedMonotoneRadiusChain.toHierarchy_effectiveRadius
#print axioms BoundedMonotoneRadiusChain.effectivePartition_fiber
#print axioms BoundedMonotoneRadiusChain.normalizedSourceCover_eq_intervalCover
#print axioms BoundedMonotoneRadiusChain.normalizedSourceCover_fiberDeltaMax
#print axioms BoundedMonotoneRadiusChain.ofAdjacentInterval_intervalCover_zero
#print axioms CoherentExactHierarchyFamily.ofFiniteScaleSequence
#print axioms CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_zero
#print axioms CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_one
#print axioms CoherentExactHierarchyFamily.toBufferedChainFamily

end

end FamilyStickyScaleChainCoherentExactHierarchyProducerV2
