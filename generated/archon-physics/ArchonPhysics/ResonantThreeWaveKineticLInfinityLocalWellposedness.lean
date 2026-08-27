import ArchonPhysics.ResonantThreeWaveKineticAELipschitz
import ArchonPhysics.ResonantThreeWaveKineticL1Lipschitz
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Unclipped local flow for the RN three-wave collision equation on canonical L-infinity

Let `nu` be the sum of the three collision-leg marginals.  This module
bundles the Radon--Nikodym collision vector as a vector field on
`Lp Real infinity nu` and proves its local Lipschitz estimate.

An `Lp` element is represented in Lean by a total function, whose values on
a null set are arbitrary.  Before applying the pointwise RN construction we
therefore project that representative to the interval determined by its own
`L-infinity` norm.  The projection is equal to the original representative
almost everywhere.  It is only a canonical choice of representative; it is
not a fixed-radius clipping of the state or of the differential equation.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness

open MeasureTheory Metric Set
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticAEBounded
open ArchonPhysics.ResonantThreeWaveKineticAELipschitz
open ArchonPhysics.ResonantThreeWaveKineticL1Lipschitz
open scoped ENNReal NNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The canonical `L-infinity` phase space for a collision measure. -/
abbrev CanonicalLInfinity (collision : ResonantThreeWaveMeasure Mode) :=
  Lp Real ∞ (collisionReferenceMeasure collision)

/-- A pointwise bounded measurable representative of a canonical
`L-infinity` class.  The radius depends on the class itself, so this does
not alter the (unclipped) vector field in the quotient. -/
def linfinityRepresentative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) : Mode → Real :=
  fun mode ↦
    (projIcc (-‖action‖) ‖action‖ (neg_le_self (norm_nonneg action))
      (action mode) : Real)

theorem measurable_linfinityRepresentative
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    Measurable (linfinityRepresentative collision action) := by
  exact (continuous_subtype_val.comp continuous_projIcc).measurable.comp
    (Lp.stronglyMeasurable action).measurable

theorem norm_linfinityRepresentative_le
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) (mode : Mode) :
    ‖linfinityRepresentative collision action mode‖ ≤ ‖action‖ := by
  change |(projIcc (-‖action‖) ‖action‖
    (neg_le_self (norm_nonneg action)) (action mode) : Real)| ≤ ‖action‖
  exact abs_le.mpr
    (projIcc (-‖action‖) ‖action‖
      (neg_le_self (norm_nonneg action)) (action mode)).property

/-- The bounded representative is the original `L-infinity` representative
almost everywhere.  Thus its projection changes only quotient-invisible
values. -/
theorem linfinityRepresentative_ae_eq
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    linfinityRepresentative collision action =ᵐ[
        collisionReferenceMeasure collision] action := by
  have hbound : ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖action mode‖ ≤ ‖action‖ := by
    have h := ae_le_lpNorm_exponent_top (Lp.memLp action)
    simpa only [Lp.norm_def,
      toReal_eLpNorm (Lp.aestronglyMeasurable action)] using h
  filter_upwards [hbound] with mode hmode
  have hmem : action mode ∈ Icc (-‖action‖) ‖action‖ := by
    rw [Real.norm_eq_abs] at hmode
    exact abs_le.mp hmode
  simp only [linfinityRepresentative]
  exact congrArg Subtype.val (projIcc_of_mem _ hmem)

/-- The RN collision vector of the canonical representative belongs to the
same canonical `L-infinity` space. -/
theorem collisionVector_memLp_top
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    MemLp (collisionVector collision
      (linfinityRepresentative collision action)) ∞
      (collisionReferenceMeasure collision) := by
  apply memLp_top_of_bound
    (measurable_collisionVector collision
      (linfinityRepresentative collision action)).aestronglyMeasurable
    (3 * ‖action‖ ^ 2)
  exact collisionVector_norm_le_ae collision
    (measurable_linfinityRepresentative collision action)
    (norm_linfinityRepresentative_le collision action)

/-- The unclipped RN collision map on the canonical `L-infinity` quotient. -/
def collisionMap
    (collision : ResonantThreeWaveMeasure Mode) :
    CanonicalLInfinity collision → CanonicalLInfinity collision :=
  fun action ↦
    (collisionVector_memLp_top collision action).toLp
      (collisionVector collision
        (linfinityRepresentative collision action))

/-- The quotient map is represented by the pointwise RN collision vector
of the canonical bounded representative. -/
theorem coeFn_collisionMap_ae_eq
    (collision : ResonantThreeWaveMeasure Mode)
    (action : CanonicalLInfinity collision) :
    collisionMap collision action =ᵐ[collisionReferenceMeasure collision]
      collisionVector collision (linfinityRepresentative collision action) :=
  MemLp.coeFn_toLp (collisionVector_memLp_top collision action)

/-- A bounded measurable representative has an essentially bounded RN
collision vector. -/
theorem collisionVector_memLp_top_of_bound
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode → Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : ∀ mode, ‖action mode‖ ≤ radius) :
    MemLp (collisionVector collision action) ∞
      (collisionReferenceMeasure collision) := by
  apply memLp_top_of_bound
    (measurable_collisionVector collision action).aestronglyMeasurable
    (3 * radius ^ 2)
  exact collisionVector_norm_le_ae collision haction_measurable haction

/-- Representative-independence certificate for the quotient lift.  Every
bounded measurable representative of the input class gives the same output
class, even when its pointwise bound differs from the class norm. -/
theorem collisionMap_eq_toLp_of_ae_eq
    (collision : ResonantThreeWaveMeasure Mode)
    (classAction : CanonicalLInfinity collision)
    {action : Mode → Real} {radius : Real}
    (haction_measurable : Measurable action)
    (haction : ∀ mode, ‖action mode‖ ≤ radius)
    (hae : action =ᵐ[collisionReferenceMeasure collision] classAction) :
    collisionMap collision classAction =
      (collisionVector_memLp_top_of_bound collision
        haction_measurable haction).toLp
        (collisionVector collision action) := by
  let commonRadius := max ‖classAction‖ radius
  have hcommonRadius : 0 ≤ commonRadius :=
    (norm_nonneg classAction).trans (le_max_left _ _)
  have hclassBound : ∀ mode,
      ‖linfinityRepresentative collision classAction mode‖ ≤ commonRadius :=
    fun mode ↦ (norm_linfinityRepresentative_le collision classAction mode).trans
      (le_max_left _ _)
  have hactionBound : ∀ mode, ‖action mode‖ ≤ commonRadius :=
    fun mode ↦ (haction mode).trans (le_max_right _ _)
  have hcollision : collisionVector collision
      (linfinityRepresentative collision classAction) =ᵐ[
        collisionReferenceMeasure collision] collisionVector collision action :=
    collisionVector_ae_eq_of_action_ae_eq collision hcommonRadius
      (measurable_linfinityRepresentative collision classAction)
      haction_measurable hclassBound hactionBound
      ((linfinityRepresentative_ae_eq collision classAction).trans hae.symm)
  apply Lp.ext
  exact (coeFn_collisionMap_ae_eq collision classAction).trans
    (hcollision.trans
      (MemLp.coeFn_toLp
        (collisionVector_memLp_top_of_bound collision
          haction_measurable haction)).symm)

/-! ## Essential-distance repair -/

/-- The measurable set where two representatives satisfy a prescribed
pointwise distance bound. -/
def distanceGoodSet (action₁ action₂ : Mode → Real) (epsilon : Real) : Set Mode :=
  {mode | ‖action₁ mode - action₂ mode‖ ≤ epsilon}

theorem measurableSet_distanceGoodSet
    {action₁ action₂ : Mode → Real}
    (haction₁ : Measurable action₁) (haction₂ : Measurable action₂)
    (epsilon : Real) :
    MeasurableSet (distanceGoodSet action₁ action₂ epsilon) := by
  exact measurableSet_le (haction₁.sub haction₂).norm measurable_const

/-- Replace the first representative by zero on the exceptional set where
the desired pairwise distance estimate fails. -/
def leftDistanceRepair (action₁ action₂ : Mode → Real) (epsilon : Real) :
    Mode → Real := by
  classical
  exact fun mode ↦ if mode ∈ distanceGoodSet action₁ action₂ epsilon
      then action₁ mode else 0

/-- Replace the second representative by zero on the same exceptional set. -/
def rightDistanceRepair (action₁ action₂ : Mode → Real) (epsilon : Real) :
    Mode → Real := by
  classical
  exact fun mode ↦ if mode ∈ distanceGoodSet action₁ action₂ epsilon
      then action₂ mode else 0

theorem measurable_leftDistanceRepair
    {action₁ action₂ : Mode → Real}
    (haction₁ : Measurable action₁) (haction₂ : Measurable action₂)
    (epsilon : Real) :
    Measurable (leftDistanceRepair action₁ action₂ epsilon) := by
  exact Measurable.ite
    (measurableSet_distanceGoodSet haction₁ haction₂ epsilon)
    haction₁ measurable_const

theorem measurable_rightDistanceRepair
    {action₁ action₂ : Mode → Real}
    (haction₁ : Measurable action₁) (haction₂ : Measurable action₂)
    (epsilon : Real) :
    Measurable (rightDistanceRepair action₁ action₂ epsilon) := by
  exact Measurable.ite
    (measurableSet_distanceGoodSet haction₁ haction₂ epsilon)
    haction₂ measurable_const

omit [MeasurableSpace Mode] in
theorem norm_leftDistanceRepair_le
    {action₁ action₂ : Mode → Real} {radius epsilon : Real}
    (hradius : 0 ≤ radius) (haction₁ : ∀ mode, ‖action₁ mode‖ ≤ radius)
    (mode : Mode) :
    ‖leftDistanceRepair action₁ action₂ epsilon mode‖ ≤ radius := by
  by_cases hmode : mode ∈ distanceGoodSet action₁ action₂ epsilon
  · simpa [leftDistanceRepair, hmode] using haction₁ mode
  · simp [leftDistanceRepair, hmode, hradius]

omit [MeasurableSpace Mode] in
theorem norm_rightDistanceRepair_le
    {action₁ action₂ : Mode → Real} {radius epsilon : Real}
    (hradius : 0 ≤ radius) (haction₂ : ∀ mode, ‖action₂ mode‖ ≤ radius)
    (mode : Mode) :
    ‖rightDistanceRepair action₁ action₂ epsilon mode‖ ≤ radius := by
  by_cases hmode : mode ∈ distanceGoodSet action₁ action₂ epsilon
  · simpa [rightDistanceRepair, hmode] using haction₂ mode
  · simp [rightDistanceRepair, hmode, hradius]

omit [MeasurableSpace Mode] in
theorem norm_distanceRepairs_sub_le
    (action₁ action₂ : Mode → Real) {epsilon : Real}
    (hepsilon : 0 ≤ epsilon) (mode : Mode) :
    ‖leftDistanceRepair action₁ action₂ epsilon mode -
        rightDistanceRepair action₁ action₂ epsilon mode‖ ≤ epsilon := by
  by_cases hmode : mode ∈ distanceGoodSet action₁ action₂ epsilon
  · have hbound : ‖action₁ mode - action₂ mode‖ ≤ epsilon := hmode
    simpa only [leftDistanceRepair, rightDistanceRepair, if_pos hmode] using hbound
  · simp [leftDistanceRepair, rightDistanceRepair, hmode, hepsilon]

theorem leftDistanceRepair_ae_eq
    {reference : Measure Mode} {action₁ action₂ : Mode → Real}
    {epsilon : Real}
    (hdistance : ∀ᵐ mode ∂reference,
      ‖action₁ mode - action₂ mode‖ ≤ epsilon) :
    leftDistanceRepair action₁ action₂ epsilon =ᵐ[reference] action₁ := by
  filter_upwards [hdistance] with mode hmode
  have hgood : mode ∈ distanceGoodSet action₁ action₂ epsilon := hmode
  simp only [leftDistanceRepair, if_pos hgood]

theorem rightDistanceRepair_ae_eq
    {reference : Measure Mode} {action₁ action₂ : Mode → Real}
    {epsilon : Real}
    (hdistance : ∀ᵐ mode ∂reference,
      ‖action₁ mode - action₂ mode‖ ≤ epsilon) :
    rightDistanceRepair action₁ action₂ epsilon =ᵐ[reference] action₂ := by
  filter_upwards [hdistance] with mode hmode
  have hgood : mode ∈ distanceGoodSet action₁ action₂ epsilon := hmode
  simp only [rightDistanceRepair, if_pos hgood]

/-- The pointwise AE-Lipschitz theorem remains valid when the input distance
hypothesis is only almost everywhere.  Both representatives are changed to
zero on the common exceptional set, so this is a representative repair,
not a clipping of the state. -/
theorem collisionVector_sub_norm_le_ae_of_ae_distance
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode → Real} {radius epsilon : Real}
    (hradius : 0 ≤ radius) (hepsilon : 0 ≤ epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : ∀ mode, ‖action₁ mode‖ ≤ radius)
    (haction₂ : ∀ mode, ‖action₂ mode‖ ≤ radius)
    (hdistance : ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖action₁ mode - action₂ mode‖ ≤ epsilon) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖ ≤
        6 * radius * epsilon := by
  let repaired₁ := leftDistanceRepair action₁ action₂ epsilon
  let repaired₂ := rightDistanceRepair action₁ action₂ epsilon
  have hrepaired₁_measurable : Measurable repaired₁ :=
    measurable_leftDistanceRepair
      haction₁_measurable haction₂_measurable epsilon
  have hrepaired₂_measurable : Measurable repaired₂ :=
    measurable_rightDistanceRepair
      haction₁_measurable haction₂_measurable epsilon
  have hrepaired₁ : ∀ mode, ‖repaired₁ mode‖ ≤ radius :=
    norm_leftDistanceRepair_le hradius haction₁
  have hrepaired₂ : ∀ mode, ‖repaired₂ mode‖ ≤ radius :=
    norm_rightDistanceRepair_le hradius haction₂
  have hrepairedDistance : ∀ mode,
      ‖repaired₁ mode - repaired₂ mode‖ ≤ epsilon :=
    norm_distanceRepairs_sub_le action₁ action₂ hepsilon
  have hcollision₁ : collisionVector collision action₁ =ᵐ[
      collisionReferenceMeasure collision] collisionVector collision repaired₁ :=
    collisionVector_ae_eq_of_action_ae_eq collision hradius
      haction₁_measurable hrepaired₁_measurable haction₁ hrepaired₁
      (leftDistanceRepair_ae_eq hdistance).symm
  have hcollision₂ : collisionVector collision action₂ =ᵐ[
      collisionReferenceMeasure collision] collisionVector collision repaired₂ :=
    collisionVector_ae_eq_of_action_ae_eq collision hradius
      haction₂_measurable hrepaired₂_measurable haction₂ hrepaired₂
      (rightDistanceRepair_ae_eq hdistance).symm
  have hrepairedBound := collisionVector_sub_norm_le_ae collision
    hradius hepsilon hrepaired₁_measurable hrepaired₂_measurable
    hrepaired₁ hrepaired₂ hrepairedDistance
  filter_upwards [hcollision₁, hcollision₂, hrepairedBound]
    with mode h₁ h₂ hbound
  simpa only [h₁, h₂] using hbound

/-! ## Quotient-level local Lipschitz estimate -/

/-- The canonical representatives inherit the essential-supremum distance
of their `L-infinity` classes. -/
theorem linfinityRepresentative_sub_norm_le_ae
    (collision : ResonantThreeWaveMeasure Mode)
    (action₁ action₂ : CanonicalLInfinity collision) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖linfinityRepresentative collision action₁ mode -
        linfinityRepresentative collision action₂ mode‖ ≤
        ‖action₁ - action₂‖ := by
  have hrepresentative₁ := linfinityRepresentative_ae_eq collision action₁
  have hrepresentative₂ := linfinityRepresentative_ae_eq collision action₂
  have hsub := Lp.coeFn_sub action₁ action₂
  have hbound₀ := ae_le_lpNorm_exponent_top (Lp.memLp (action₁ - action₂))
  have hbound : ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖(action₁ - action₂) mode‖ ≤ ‖action₁ - action₂‖ := by
    simpa only [Lp.norm_def,
      toReal_eLpNorm (Lp.aestronglyMeasurable (action₁ - action₂))] using hbound₀
  filter_upwards [hrepresentative₁, hrepresentative₂, hsub, hbound]
    with mode h₁ h₂ hsubmode hmode
  simp only [Pi.sub_apply] at hsubmode
  rw [h₁, h₂, ← hsubmode]
  exact hmode

/-- On every origin-centered `L-infinity` ball of radius `R`, the unclipped
collision map is `6R`-Lipschitz. -/
theorem norm_collisionMap_sub_le
    (collision : ResonantThreeWaveMeasure Mode)
    {radius : Real} (hradius : 0 ≤ radius)
    (action₁ action₂ : CanonicalLInfinity collision)
    (haction₁ : ‖action₁‖ ≤ radius) (haction₂ : ‖action₂‖ ≤ radius) :
    ‖collisionMap collision action₁ - collisionMap collision action₂‖ ≤
      6 * radius * ‖action₁ - action₂‖ := by
  let representative₁ := linfinityRepresentative collision action₁
  let representative₂ := linfinityRepresentative collision action₂
  have hrepresentative₁ : ∀ mode, ‖representative₁ mode‖ ≤ radius := fun mode ↦
    (norm_linfinityRepresentative_le collision action₁ mode).trans haction₁
  have hrepresentative₂ : ∀ mode, ‖representative₂ mode‖ ≤ radius := fun mode ↦
    (norm_linfinityRepresentative_le collision action₂ mode).trans haction₂
  have hcollision := collisionVector_sub_norm_le_ae_of_ae_distance collision
    hradius (norm_nonneg (action₁ - action₂))
    (measurable_linfinityRepresentative collision action₁)
    (measurable_linfinityRepresentative collision action₂)
    hrepresentative₁ hrepresentative₂
    (linfinityRepresentative_sub_norm_le_ae collision action₁ action₂)
  have houtput : ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖(collisionMap collision action₁ - collisionMap collision action₂) mode‖ ≤
        6 * radius * ‖action₁ - action₂‖ := by
    filter_upwards [Lp.coeFn_sub (collisionMap collision action₁)
        (collisionMap collision action₂),
      coeFn_collisionMap_ae_eq collision action₁,
      coeFn_collisionMap_ae_eq collision action₂, hcollision]
      with mode hsub h₁ h₂ hbound
    simp only [Pi.sub_apply] at hsub
    rw [hsub, h₁, h₂]
    exact hbound
  have hK : 0 ≤ 6 * radius * ‖action₁ - action₂‖ := by positivity
  have hess := eLpNormEssSup_le_of_ae_bound houtput
  calc
    ‖collisionMap collision action₁ - collisionMap collision action₂‖ =
        (eLpNormEssSup
          (collisionMap collision action₁ - collisionMap collision action₂)
          (collisionReferenceMeasure collision)).toReal := by
      rw [Lp.norm_def, eLpNorm_exponent_top]
    _ ≤ (ENNReal.ofReal (6 * radius * ‖action₁ - action₂‖)).toReal :=
      ENNReal.toReal_mono (by simp) hess
    _ = 6 * radius * ‖action₁ - action₂‖ := ENNReal.toReal_ofReal hK

/-- Bundled `6R` Lipschitz estimate on the closed origin ball. -/
theorem lipschitzOnWith_collisionMap_closedBall_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (radius : Real) (hradius : 0 ≤ radius) :
    LipschitzOnWith (Real.toNNReal (6 * radius)) (collisionMap collision)
      (closedBall (0 : CanonicalLInfinity collision) radius) := by
  refine LipschitzOnWith.of_dist_le_mul fun action₁ haction₁ action₂ haction₂ ↦ ?_
  have hnorm₁ : ‖action₁‖ ≤ radius := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using haction₁
  have hnorm₂ : ‖action₂‖ ≤ radius := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using haction₂
  have hbound := norm_collisionMap_sub_le collision hradius
    action₁ action₂ hnorm₁ hnorm₂
  simpa only [dist_eq_norm,
    Real.coe_toNNReal (6 * radius) (by positivity : 0 ≤ 6 * radius)] using hbound

/-- The unclipped quotient collision map is locally Lipschitz on all of
canonical `L-infinity`. -/
theorem locallyLipschitz_collisionMap
    (collision : ResonantThreeWaveMeasure Mode) :
    LocallyLipschitz (collisionMap collision) := by
  intro action
  let radius : Real := ‖action‖ + 1
  have hradius : 0 ≤ radius := add_nonneg (norm_nonneg action) zero_le_one
  have hmem : action ∈ ball (0 : CanonicalLInfinity collision) radius := by
    rw [mem_ball, dist_zero_right]
    dsimp [radius]
    linarith
  refine ⟨Real.toNNReal (6 * radius),
    ball (0 : CanonicalLInfinity collision) radius,
    isOpen_ball.mem_nhds hmem, ?_⟩
  exact (lipschitzOnWith_collisionMap_closedBall_zero
    collision radius hradius).mono ball_subset_closedBall

/-- In particular, the unclipped collision map is continuous. -/
theorem continuous_collisionMap
    (collision : ResonantThreeWaveMeasure Mode) :
    Continuous (collisionMap collision) :=
  (locallyLipschitz_collisionMap collision).continuous

/-! ## Coupling-scaled vector field -/

/-- The coupling-scaled, unclipped RN collision vector field. -/
def rnCollisionVectorField
    (collision : ResonantThreeWaveMeasure Mode) (g : Real) :
    CanonicalLInfinity collision → CanonicalLInfinity collision :=
  fun action ↦ g ^ 2 • collisionMap collision action

/-- A trajectory solves the unclipped RN collision ODE on a symmetric
closed time interval. -/
def SolvesRNCollisionODEOn
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (initial : CanonicalLInfinity collision) (ε : Real)
    (D : Real → CanonicalLInfinity collision) : Prop :=
  D 0 = initial ∧
    ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt D (rnCollisionVectorField collision g (D t))
        (Icc (-ε) ε) t

/-- A canonical `L-infinity` trajectory remains in the prescribed ball
around its initial datum. -/
def RemainsInCanonicalLInfinityBall
    (collision : ResonantThreeWaveMeasure Mode)
    (initial : CanonicalLInfinity collision) (a : NNReal) (ε : Real)
    (D : Real → CanonicalLInfinity collision) : Prop :=
  ∀ t ∈ Icc (-ε) ε, D t ∈ closedBall initial (a : Real)

/-- A ball about `initial` of radius `a` is contained in the origin ball of
radius `‖initial‖ + a`. -/
theorem closedBall_subset_closedBall_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (initial : CanonicalLInfinity collision) (a : NNReal) :
    closedBall initial (a : Real) ⊆
      closedBall (0 : CanonicalLInfinity collision) (‖initial‖ + (a : Real)) := by
  intro action haction
  rw [mem_closedBall_iff_norm] at haction ⊢
  simp only [sub_zero]
  calc
    ‖action‖ ≤ ‖action - initial‖ + ‖initial‖ := norm_le_norm_sub_add _ _
    _ ≤ (a : Real) + ‖initial‖ := by gcongr
    _ = ‖initial‖ + (a : Real) := add_comm _ _

/-- The collision map is Lipschitz on every ball about an arbitrary center,
with the explicit common norm radius `‖initial‖ + a`. -/
theorem lipschitzOnWith_collisionMap_closedBall
    (collision : ResonantThreeWaveMeasure Mode)
    (initial : CanonicalLInfinity collision) (a : NNReal) :
    LipschitzOnWith
      (Real.toNNReal (6 * (‖initial‖ + (a : Real))))
      (collisionMap collision) (closedBall initial (a : Real)) := by
  have hradius : 0 ≤ ‖initial‖ + (a : Real) := by positivity
  exact (lipschitzOnWith_collisionMap_closedBall_zero collision
    (‖initial‖ + (a : Real)) hradius).mono
      (closedBall_subset_closedBall_zero collision initial a)

/-- Scaling by `g²` scales the local Lipschitz constant by `‖g²‖`. -/
theorem lipschitzOnWith_rnCollisionVectorField_closedBall
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (initial : CanonicalLInfinity collision) (a : NNReal) :
    LipschitzOnWith
      (‖g ^ 2‖₊ * Real.toNNReal (6 * (‖initial‖ + (a : Real))))
      (rnCollisionVectorField collision g)
      (closedBall initial (a : Real)) := by
  let K : NNReal := Real.toNNReal (6 * (‖initial‖ + (a : Real)))
  have hcollision : LipschitzOnWith K (collisionMap collision)
      (closedBall initial (a : Real)) :=
    lipschitzOnWith_collisionMap_closedBall collision initial a
  refine LipschitzOnWith.of_dist_le_mul fun action₁ haction₁ action₂ haction₂ ↦ ?_
  change dist
      (g ^ 2 • collisionMap collision action₁)
      (g ^ 2 • collisionMap collision action₂) ≤
    (((‖g ^ 2‖₊ * K : NNReal) : Real) * dist action₁ action₂)
  calc
    dist
        (g ^ 2 • collisionMap collision action₁)
        (g ^ 2 • collisionMap collision action₂) ≤
      ‖g ^ 2‖ * dist
        (collisionMap collision action₁) (collisionMap collision action₂) :=
      dist_smul_le _ _ _
    _ ≤ ‖g ^ 2‖ * ((K : Real) * dist action₁ action₂) := by
      gcongr
      exact hcollision.dist_le_mul action₁ haction₁ action₂ haction₂
    _ = (((‖g ^ 2‖₊ * K : NNReal) : Real) * dist action₁ action₂) := by
      simp [mul_assoc]

/-- The coupling-scaled unclipped field is locally Lipschitz. -/
theorem locallyLipschitz_rnCollisionVectorField
    (collision : ResonantThreeWaveMeasure Mode) (g : Real) :
    LocallyLipschitz (rnCollisionVectorField collision g) := by
  intro initial
  refine ⟨‖g ^ 2‖₊ * Real.toNNReal (6 * (‖initial‖ + 1)),
    ball initial 1, isOpen_ball.mem_nhds (mem_ball_self zero_lt_one), ?_⟩
  have hball : ball initial 1 ⊆ closedBall initial (1 : Real) :=
    ball_subset_closedBall
  simpa only [NNReal.coe_one] using
    (lipschitzOnWith_rnCollisionVectorField_closedBall
      collision g initial 1).mono hball

/--
Every initial canonical `L-infinity` class has a positive-time solution of
the genuine, unclipped RN collision ODE.  The solution stays in any chosen
positive ball about the initial datum and is unique among solutions staying
in that ball.
-/
theorem exists_unique_local_rnCollisionODE
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (initial : CanonicalLInfinity collision)
    (a : NNReal) (ha : 0 < a) :
    ∃ ε : Real, 0 < ε ∧
      ∃ D : Real → CanonicalLInfinity collision,
        SolvesRNCollisionODEOn collision g initial ε D ∧
        RemainsInCanonicalLInfinityBall collision initial a ε D ∧
        ∀ E : Real → CanonicalLInfinity collision,
          SolvesRNCollisionODEOn collision g initial ε E →
          RemainsInCanonicalLInfinityBall collision initial a ε E →
          EqOn D E (Icc (-ε) ε) := by
  let X := CanonicalLInfinity collision
  let F : X → X := rnCollisionVectorField collision g
  let Kf : NNReal := ‖g ^ 2‖₊ *
    Real.toNNReal (6 * (‖initial‖ + (a : Real)))
  let L : NNReal := Kf * a + ‖F initial‖₊
  let ε : Real := (a : Real) / ((L : Real) + 1)
  have hapos : 0 < (a : Real) := NNReal.coe_pos.2 ha
  have hdenpos : 0 < (L : Real) + 1 := by positivity
  have hεpos : 0 < ε := div_pos hapos hdenpos
  have hFlip : LipschitzOnWith Kf F (closedBall initial (a : Real)) := by
    exact lipschitzOnWith_rnCollisionVectorField_closedBall
      collision g initial a
  have hcenter : initial ∈ closedBall initial (a : Real) :=
    mem_closedBall_self hapos.le
  have hbound : ∀ x ∈ closedBall initial (a : Real), ‖F x‖ ≤ (L : Real) := by
    intro x hx
    calc
      ‖F x‖ ≤ ‖F x - F initial‖ + ‖F initial‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ (Kf : Real) * ‖x - initial‖ + ‖F initial‖ := by
        gcongr
        exact hFlip.norm_sub_le hx hcenter
      _ ≤ (Kf : Real) * (a : Real) + ‖F initial‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact hx
      _ = (L : Real) := by simp [L]
  let t₀ : Icc (-ε) ε := ⟨0, by constructor <;> linarith⟩
  have hwindow :
      (L : Real) * max (ε - (t₀ : Real)) ((t₀ : Real) - (-ε)) ≤
        (a : Real) - (0 : Real) := by
    simp only [t₀, sub_zero, zero_sub, neg_neg, max_self]
    change (L : Real) * ((a : Real) / ((L : Real) + 1)) ≤ (a : Real)
    calc
      (L : Real) * ((a : Real) / ((L : Real) + 1)) =
          ((L : Real) / ((L : Real) + 1)) * (a : Real) := by ring
      _ ≤ 1 * (a : Real) := by
        gcongr
        exact (div_le_one hdenpos).2 (by linarith)
      _ = (a : Real) := one_mul _
  have hpl : IsPicardLindelof (fun _ : Real ↦ F) t₀ initial a 0 L Kf :=
    IsPicardLindelof.of_time_independent hbound hFlip hwindow
  have hinitial : initial ∈ closedBall initial (((0 : NNReal) : Real)) :=
    mem_closedBall_self le_rfl
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl hinitial
  let D : Real → X := α.compProj
  have hD0 : D 0 = initial := by
    change α.compProj (t₀ : Real) = initial
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  have hDderiv : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt D (F (D t)) (Icc (-ε) ε) t := by
    intro t ht
    dsimp only [D]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hpl.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ ↦ α.compProj_mem_closedBall hpl.mul_max_le)
      initial ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  have hDmem :
      RemainsInCanonicalLInfinityBall collision initial a ε D := by
    intro t ht
    exact α.compProj_mem_closedBall hpl.mul_max_le
  refine ⟨ε, hεpos, D, ?_, hDmem, ?_⟩
  · exact ⟨hD0, by simpa [F] using hDderiv⟩
  · intro E hE hEmem
    apply ODE_solution_unique_of_mem_Icc
      (v := fun _ : Real ↦ F)
      (s := fun _ : Real ↦ closedBall initial (a : Real))
      (K := Kf) (t₀ := 0)
    · intro t ht
      exact hFlip
    · constructor <;> linarith
    · exact HasDerivWithinAt.continuousOn hDderiv
    · intro t ht
      apply (hDderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
      exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
    · intro t ht
      exact hDmem t (Ioo_subset_Icc_self ht)
    · exact HasDerivWithinAt.continuousOn hE.2
    · intro t ht
      apply (hE.2 t (Ioo_subset_Icc_self ht)).hasDerivAt
      exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
    · intro t ht
      exact hEmem t (Ioo_subset_Icc_self ht)
    · exact hD0.trans hE.1.symm


end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
