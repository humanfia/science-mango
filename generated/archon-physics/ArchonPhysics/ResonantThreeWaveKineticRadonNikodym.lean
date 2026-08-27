import ArchonPhysics.ResonantThreeWaveKineticBridge
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Radon--Nikodym collision operator of a resonant three-wave measure

For a finite collision measure on ordered triads, the three coordinate
pushforwards provide a canonical finite mode reference measure.  If an action
is bounded and measurable, its three-wave flux is an integrable signed density
on triad space.  Pushing that signed density along the parent leg and
subtracting its two child-leg pushforwards gives a finite signed collision
measure on mode space.

This signed measure is absolutely continuous with respect to the sum of the
three leg marginals.  Its signed Radon--Nikodym derivative is consequently a
canonical pointwise collision operator.  The module proves both the exact
measure representation and the ordinary Bochner weak-pairing identity for
bounded measurable actions and tests.

The boundedness restriction is explicit.  No continuum ODE well-posedness,
positivity preservation, relaxation, or microscopic kinetic limit is asserted.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticBridge
open ArchonPhysics.ThreeWaveCollisionAlgebra
open scoped MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A real-valued function together with the exact regularity used by the
continuum collision construction: measurability and a global norm bound. -/
structure IsBoundedMeasurable (f : Mode -> Real) : Prop where
  measurable : Measurable f
  exists_norm_bound : Exists fun bound : Real => forall mode, norm (f mode) <= bound

/-- Extract one coordinate of an ordered three-mode collision. -/
def triadLeg (leg : Fin 3) : (Fin 3 -> Mode) -> Mode :=
  fun triad => triad leg

/-- Every coordinate projection from triad space is measurable. -/
theorem measurable_triadLeg (leg : Fin 3) : Measurable (triadLeg leg :
    (Fin 3 -> Mode) -> Mode) := by
  exact measurable_pi_apply leg

/-- The positive marginal of the collision measure carried by one leg. -/
def legMarginal (collision : ResonantThreeWaveMeasure Mode) (leg : Fin 3) :
    Measure Mode :=
  Measure.map (triadLeg leg) collision.collisionMeasure

/-- The canonical mode reference measure is the sum of all three leg
marginals.  It contains every mode occurrence that can contribute to the weak
collision functional. -/
def collisionReferenceMeasure (collision : ResonantThreeWaveMeasure Mode) :
    Measure Mode :=
  legMarginal collision 0 + legMarginal collision 1 + legMarginal collision 2

/-- A leg marginal is finite because it is a pushforward of the supplied
finite collision measure. -/
instance instIsFiniteMeasureLegMarginal
    (collision : ResonantThreeWaveMeasure Mode) (leg : Fin 3) :
    IsFiniteMeasure (legMarginal collision leg) :=
  (collision.collisionMeasure : Measure (Fin 3 -> Mode)).isFiniteMeasure_map _

/-- The sum of the three finite leg marginals is finite. -/
instance instIsFiniteMeasureCollisionReference
    (collision : ResonantThreeWaveMeasure Mode) :
    IsFiniteMeasure (collisionReferenceMeasure collision) := by
  unfold collisionReferenceMeasure
  infer_instance

/-- Every leg marginal is dominated by the canonical reference measure. -/
theorem legMarginal_le_collisionReferenceMeasure
    (collision : ResonantThreeWaveMeasure Mode) (leg : Fin 3) :
    legMarginal collision leg <= collisionReferenceMeasure collision := by
  fin_cases leg
  · exact (Measure.le_add_right (Measure.le_add_right le_rfl))
  · exact (Measure.le_add_right (Measure.le_add_left le_rfl))
  · exact Measure.le_add_left le_rfl

/-- The collision flux regarded as a scalar function on ordered triads. -/
def triadFlux (action : Mode -> Real) (triad : Fin 3 -> Mode) : Real :=
  collisionFlux (action (triad 0)) (action (triad 1)) (action (triad 2))

/-- Measurable actions give a measurable triad flux. -/
theorem measurable_triadFlux {action : Mode -> Real}
    (haction : Measurable action) : Measurable (triadFlux action) := by
  unfold triadFlux collisionFlux
  fun_prop

omit [MeasurableSpace Mode] in
/-- A global bound on the action gives the explicit quadratic flux bound
`3 * bound^2`. -/
theorem norm_triadFlux_le
    {action : Mode -> Real} {bound : Real}
    (haction : forall mode, norm (action mode) <= bound)
    (triad : Fin 3 -> Mode) :
    norm (triadFlux action triad) <= 3 * bound ^ 2 := by
  have hbound_nonneg : 0 <= bound :=
    (norm_nonneg (action (triad 0))).trans (haction (triad 0))
  have hmul (i j : Fin 3) :
      norm (action (triad i) * action (triad j)) <= bound ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul (haction (triad i)) (haction (triad j))
      (norm_nonneg _) hbound_nonneg
  unfold triadFlux collisionFlux
  calc
    norm
        (action (triad 1) * action (triad 2) -
          action (triad 0) * action (triad 1) -
          action (triad 0) * action (triad 2)) <=
        norm (action (triad 1) * action (triad 2)) +
          norm (action (triad 0) * action (triad 1)) +
          norm (action (triad 0) * action (triad 2)) := by
      calc
        _ <= norm
              (action (triad 1) * action (triad 2) -
                action (triad 0) * action (triad 1)) +
              norm (action (triad 0) * action (triad 2)) := norm_sub_le _ _
        _ <= _ := by gcongr; exact norm_sub_le _ _
    _ <= bound ^ 2 + bound ^ 2 + bound ^ 2 := by
      gcongr <;> apply hmul
    _ = 3 * bound ^ 2 := by ring

/-- A bounded measurable action has an integrable flux against every finite
resonant collision measure. -/
theorem integrable_triadFlux (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode -> Real} (haction : IsBoundedMeasurable action) :
    Integrable (triadFlux action) collision.collisionMeasure := by
  obtain ⟨bound, hbound⟩ := haction.exists_norm_bound
  apply Integrable.of_bound
    (measurable_triadFlux haction.measurable).aestronglyMeasurable
    (3 * bound ^ 2)
  exact Filter.Eventually.of_forall (norm_triadFlux_le hbound)

/-- Signed triad measure whose density is the nonlinear collision flux. -/
def fluxSignedTriadMeasure (collision : ResonantThreeWaveMeasure Mode)
    (action : Mode -> Real) : SignedMeasure (Fin 3 -> Mode) :=
  (collision.collisionMeasure : Measure (Fin 3 -> Mode)).withDensityᵥ
    (triadFlux action)

/-- Signed flux measure transported to one mode leg. -/
def legFluxSignedMeasure (collision : ResonantThreeWaveMeasure Mode)
    (action : Mode -> Real) (leg : Fin 3) : SignedMeasure Mode :=
  (fluxSignedTriadMeasure collision action).map (triadLeg leg)

/-- Net signed collision measure on mode space, with reaction convention
`parent - child_1 - child_2`. -/
def signedCollisionMeasure (collision : ResonantThreeWaveMeasure Mode)
    (action : Mode -> Real) : SignedMeasure Mode :=
  legFluxSignedMeasure collision action 0 -
    legFluxSignedMeasure collision action 1 -
    legFluxSignedMeasure collision action 2

/-- One transported signed flux measure is absolutely continuous with respect
to its corresponding positive leg marginal. -/
theorem legFluxSignedMeasure_absolutelyContinuous_legMarginal
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (leg : Fin 3) :
    legFluxSignedMeasure collision action leg ≪ᵥ
      (legMarginal collision leg).toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  rw [legFluxSignedMeasure,
    VectorMeasure.map_apply _ (measurable_triadLeg leg) hs]
  apply Measure.withDensityᵥ_absolutelyContinuous
    (collision.collisionMeasure : Measure (Fin 3 -> Mode)) (triadFlux action)
  rw [Measure.toENNRealVectorMeasure_apply_measurable
    ((measurable_triadLeg leg) hs)]
  rw [legMarginal, Measure.toENNRealVectorMeasure_apply_measurable hs,
    Measure.map_apply (measurable_triadLeg leg) hs] at hzero
  exact hzero

/-- One transported signed leg flux is absolutely continuous with respect to
the common three-leg reference measure. -/
theorem legFluxSignedMeasure_absolutelyContinuous_reference
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real)
    (leg : Fin 3) :
    legFluxSignedMeasure collision action leg ≪ᵥ
      (collisionReferenceMeasure collision).toENNRealVectorMeasure := by
  refine (legFluxSignedMeasure_absolutelyContinuous_legMarginal
    collision action leg).trans ?_
  refine VectorMeasure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero ⊢
  exact (legMarginal_le_collisionReferenceMeasure collision leg).absolutelyContinuous hzero

/-- The net signed collision measure is absolutely continuous with respect to
the canonical reference measure. -/
theorem signedCollisionMeasure_absolutelyContinuous
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real) :
    signedCollisionMeasure collision action ≪ᵥ
      (collisionReferenceMeasure collision).toENNRealVectorMeasure := by
  exact ((legFluxSignedMeasure_absolutelyContinuous_reference
    collision action 0).sub
      (legFluxSignedMeasure_absolutelyContinuous_reference
        collision action 1)).sub
    (legFluxSignedMeasure_absolutelyContinuous_reference collision action 2)

/-- Canonical continuum pointwise collision vector: the signed RN derivative
of the net flux measure relative to the sum of its three leg marginals. -/
def collisionVector (collision : ResonantThreeWaveMeasure Mode)
    (action : Mode -> Real) : Mode -> Real :=
  (signedCollisionMeasure collision action).rnDeriv
    (collisionReferenceMeasure collision)

/-- The canonical collision vector is measurable for every action. -/
theorem measurable_collisionVector (collision : ResonantThreeWaveMeasure Mode)
    (action : Mode -> Real) : Measurable (collisionVector collision action) := by
  exact SignedMeasure.measurable_rnDeriv _ _

/-- The canonical collision vector is integrable against the three-leg
reference measure for every action. -/
theorem integrable_collisionVector (collision : ResonantThreeWaveMeasure Mode)
    (action : Mode -> Real) :
    Integrable (collisionVector collision action)
      (collisionReferenceMeasure collision) := by
  exact SignedMeasure.integrable_rnDeriv _ _

/-- Exact RN representation of the signed collision measure. -/
theorem withDensity_collisionVector_eq_signedCollisionMeasure
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real) :
    (collisionReferenceMeasure collision).withDensityᵥ
        (collisionVector collision action) =
      signedCollisionMeasure collision action := by
  exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ _
    (signedCollisionMeasure_absolutelyContinuous collision action)

/-- Pairing a bounded measurable test against a signed density is the ordinary
Bochner integral of `test * density`. -/
theorem integral_pairing_withDensityᵥ
    (reference : Measure Mode) {density test : Mode -> Real}
    (hdensity_measurable : Measurable density)
    (hdensity : Integrable density reference)
    (htest_measurable : Measurable test)
    (bound : Real) (htest_bound : forall mode, norm (test mode) <= bound) :
    (∫ᵛ mode, test mode ∂<•(reference.withDensityᵥ density)) =
      ∫ mode, test mode * density mode ∂reference := by
  let posMeasure : Measure Mode :=
    reference.withDensity (fun mode => ENNReal.ofReal (density mode))
  let negMeasure : Measure Mode :=
    reference.withDensity (fun mode => ENNReal.ofReal (-density mode))
  let _ : IsFiniteMeasure posMeasure := by
    dsimp only [posMeasure]
    exact isFiniteMeasure_withDensity_ofReal hdensity.2
  let _ : IsFiniteMeasure negMeasure := by
    dsimp only [negMeasure]
    exact isFiniteMeasure_withDensity_ofReal hdensity.neg.2
  have htest_pos : Integrable test posMeasure := by
    apply Integrable.of_bound htest_measurable.aestronglyMeasurable bound
    exact Filter.Eventually.of_forall htest_bound
  have htest_neg : Integrable test negMeasure := by
    apply Integrable.of_bound htest_measurable.aestronglyMeasurable bound
    exact Filter.Eventually.of_forall htest_bound
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hdensity]
  rw [VectorMeasure.integral_sub_vectorMeasure
    (by simpa [VectorMeasure.Integrable, posMeasure] using htest_pos)
    (by simpa [VectorMeasure.Integrable, negMeasure] using htest_neg)]
  rw [VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    hdensity_measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun mode => by simp))]
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun mode => ENNReal.ofReal (-density mode))
    hdensity_measurable.neg.ennreal_ofReal
    (Filter.Eventually.of_forall (fun mode => by simp))]
  have hweighted_pos : Integrable
      (fun mode => (ENNReal.ofReal (density mode)).toReal • test mode)
      reference :=
    (integrable_withDensity_iff_integrable_smul'
      hdensity_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun mode => by simp))).mp
      (by simpa [posMeasure] using htest_pos)
  have hweighted_neg : Integrable
      (fun mode => (ENNReal.ofReal (-density mode)).toReal • test mode)
      reference :=
    (integrable_withDensity_iff_integrable_smul'
      hdensity_measurable.neg.ennreal_ofReal
      (Filter.Eventually.of_forall (fun mode => by simp))).mp
      (by simpa [negMeasure] using htest_neg)
  rw [← integral_sub hweighted_pos hweighted_neg]
  apply integral_congr_ae
  filter_upwards with mode
  simp only [smul_eq_mul, ENNReal.toReal_ofReal']
  by_cases hnonneg : 0 <= density mode
  · rw [max_eq_left hnonneg,
      max_eq_right (by linarith : -density mode <= 0)]
    ring
  · have hnonpos : density mode <= 0 := le_of_not_ge hnonneg
    rw [max_eq_right hnonpos,
      max_eq_left (by linarith : 0 <= -density mode)]
    ring

/-- A bounded measurable test is integrable against the variation of every
finite signed measure. -/
theorem IsBoundedMeasurable.signedIntegrable
    {f : Mode -> Real} (hf : IsBoundedMeasurable f)
    (measure : SignedMeasure Mode) : measure.Integrable f := by
  let _ : IsFiniteMeasure measure.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  obtain ⟨bound, hbound⟩ := hf.exists_norm_bound
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hbound)

/-- Exact weak pairing of the net signed mode measure with the original
triad collision functional. -/
theorem signedCollisionMeasure_pairing_eq_weakCollisionSlope
    (collision : ResonantThreeWaveMeasure Mode)
    {test action : Mode -> Real}
    (htest : IsBoundedMeasurable test)
    (haction : IsBoundedMeasurable action) :
    (∫ᵛ mode, test mode ∂<•(signedCollisionMeasure collision action)) =
      weakCollisionSlope collision test action := by
  let _ : IsFiniteMeasure
      (fluxSignedTriadMeasure collision action).variation := by
    have hflux := integrable_triadFlux collision haction
    rw [fluxSignedTriadMeasure, Measure.variation_withDensityᵥ hflux]
    exact isFiniteMeasure_withDensity
      (hasFiniteIntegral_iff_enorm.mp hflux.2).ne
  have hleg_integrable (leg : Fin 3) :
      (legFluxSignedMeasure collision action leg).Integrable test :=
    htest.signedIntegrable _
  rw [signedCollisionMeasure,
    VectorMeasure.integral_sub_vectorMeasure
      ((hleg_integrable 0).sub_vectorMeasure (hleg_integrable 1))
      (hleg_integrable 2),
    VectorMeasure.integral_sub_vectorMeasure
      (hleg_integrable 0) (hleg_integrable 1)]
  have hmap (leg : Fin 3) :
      (∫ᵛ mode, test mode
          ∂<•(legFluxSignedMeasure collision action leg)) =
        ∫ᵛ triad, test (triad leg)
          ∂<•(fluxSignedTriadMeasure collision action) := by
    unfold legFluxSignedMeasure
    apply VectorMeasure.integral_map (measurable_triadLeg leg)
    · exact htest.measurable.aestronglyMeasurable
    · obtain ⟨bound, hbound⟩ := htest.exists_norm_bound
      apply Integrable.of_bound
        (htest.measurable.comp (measurable_triadLeg leg)).aestronglyMeasurable
        bound
      exact Filter.Eventually.of_forall (fun triad => hbound (triad leg))
  rw [hmap 0, hmap 1, hmap 2]
  have htriad_test (leg : Fin 3) :
      (fluxSignedTriadMeasure collision action).Integrable
        (fun triad => test (triad leg)) := by
    obtain ⟨bound, hbound⟩ := htest.exists_norm_bound
    apply Integrable.of_bound
      (htest.measurable.comp (measurable_triadLeg leg)).aestronglyMeasurable
      bound
    exact Filter.Eventually.of_forall (fun triad => hbound (triad leg))
  have hcombine :
      (∫ᵛ triad, test (triad 0)
          ∂<•(fluxSignedTriadMeasure collision action)) -
          (∫ᵛ triad, test (triad 1)
            ∂<•(fluxSignedTriadMeasure collision action)) -
          (∫ᵛ triad, test (triad 2)
            ∂<•(fluxSignedTriadMeasure collision action)) =
        ∫ᵛ triad, test (triad 0) - test (triad 1) - test (triad 2)
          ∂<•(fluxSignedTriadMeasure collision action) := by
    have hzero_one :
        (∫ᵛ triad, test (triad 0)
            ∂<•(fluxSignedTriadMeasure collision action)) -
            (∫ᵛ triad, test (triad 1)
              ∂<•(fluxSignedTriadMeasure collision action)) =
          ∫ᵛ triad, test (triad 0) - test (triad 1)
            ∂<•(fluxSignedTriadMeasure collision action) :=
      (VectorMeasure.integral_fun_sub
        (htriad_test 0) (htriad_test 1)).symm
    have hzero_one_two :
        (∫ᵛ triad, test (triad 0) - test (triad 1)
            ∂<•(fluxSignedTriadMeasure collision action)) -
            (∫ᵛ triad, test (triad 2)
              ∂<•(fluxSignedTriadMeasure collision action)) =
          ∫ᵛ triad, test (triad 0) - test (triad 1) - test (triad 2)
            ∂<•(fluxSignedTriadMeasure collision action) :=
      (VectorMeasure.integral_fun_sub
        ((htriad_test 0).sub (htriad_test 1)) (htriad_test 2)).symm
    exact (congrArg (fun value => value -
      (∫ᵛ triad, test (triad 2)
        ∂<•(fluxSignedTriadMeasure collision action))) hzero_one).trans
      hzero_one_two
  rw [hcombine]
  obtain ⟨testBound, htestBound⟩ := htest.exists_norm_bound
  have hsignedTestMeasurable : Measurable
      (fun triad : Fin 3 -> Mode =>
        test (triad 0) - test (triad 1) - test (triad 2)) := by
    exact ((htest.measurable.comp (measurable_triadLeg 0)).sub
      (htest.measurable.comp (measurable_triadLeg 1))).sub
      (htest.measurable.comp (measurable_triadLeg 2))
  have hsignedTestBound (triad : Fin 3 -> Mode) :
      norm (test (triad 0) - test (triad 1) - test (triad 2)) <=
        3 * testBound := by
    have hbound_nonneg : 0 <= testBound :=
      (norm_nonneg (test (triad 0))).trans (htestBound (triad 0))
    calc
      norm (test (triad 0) - test (triad 1) - test (triad 2)) <=
          norm (test (triad 0)) + norm (test (triad 1)) +
            norm (test (triad 2)) := by
        calc
          _ <= norm (test (triad 0) - test (triad 1)) +
              norm (test (triad 2)) := norm_sub_le _ _
          _ <= _ := by gcongr; exact norm_sub_le _ _
      _ <= testBound + testBound + testBound := by
        gcongr <;> apply htestBound
      _ = 3 * testBound := by ring
  unfold fluxSignedTriadMeasure
  rw [integral_pairing_withDensityᵥ
    (collision.collisionMeasure : Measure (Fin 3 -> Mode))
    (measurable_triadFlux haction.measurable)
    (integrable_triadFlux collision haction)
    hsignedTestMeasurable (3 * testBound) hsignedTestBound]
  unfold weakCollisionSlope triadWeakObservableIntegrand triadFlux
  apply integral_congr_ae
  filter_upwards with triad
  ring

/-- Ordinary Bochner weak-pairing identity for the canonical pointwise RN
collision vector. -/
theorem integral_test_mul_collisionVector_eq_weakCollisionSlope
    (collision : ResonantThreeWaveMeasure Mode)
    {test action : Mode -> Real}
    (htest : IsBoundedMeasurable test)
    (haction : IsBoundedMeasurable action) :
    (∫ mode, test mode * collisionVector collision action mode
      ∂collisionReferenceMeasure collision) =
      weakCollisionSlope collision test action := by
  obtain ⟨bound, hbound⟩ := htest.exists_norm_bound
  calc
    (∫ mode, test mode * collisionVector collision action mode
        ∂collisionReferenceMeasure collision) =
        ∫ᵛ mode, test mode
          ∂<•((collisionReferenceMeasure collision).withDensityᵥ
            (collisionVector collision action)) :=
      (integral_pairing_withDensityᵥ
        (collisionReferenceMeasure collision)
        (measurable_collisionVector collision action)
        (integrable_collisionVector collision action)
        htest.measurable bound hbound).symm
    _ = ∫ᵛ mode, test mode
          ∂<•(signedCollisionMeasure collision action) := by
      rw [withDensity_collisionVector_eq_signedCollisionMeasure]
    _ = weakCollisionSlope collision test action :=
      signedCollisionMeasure_pairing_eq_weakCollisionSlope
        collision htest haction

/-- The bounded-test output appearing in the weak pairing is genuinely
integrable against the canonical reference measure. -/
theorem integrable_test_mul_collisionVector
    (collision : ResonantThreeWaveMeasure Mode)
    {test action : Mode -> Real} (htest : IsBoundedMeasurable test) :
    Integrable (fun mode => test mode * collisionVector collision action mode)
      (collisionReferenceMeasure collision) := by
  obtain ⟨bound, hbound⟩ := htest.exists_norm_bound
  exact (integrable_collisionVector collision action).bdd_mul
    htest.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Proof-carrying pointwise representation valid on the explicit class of
bounded measurable actions and tests. -/
structure BoundedPointwiseCollisionRepresentation
    (collision : ResonantThreeWaveMeasure Mode) where
  reference : Measure Mode
  collisionVector : (Mode -> Real) -> Mode -> Real
  measurable_output : forall action, Measurable (collisionVector action)
  integrable_output : forall test action,
    IsBoundedMeasurable test -> IsBoundedMeasurable action ->
      Integrable (fun mode => test mode * collisionVector action mode) reference
  represents : forall test action,
    IsBoundedMeasurable test -> IsBoundedMeasurable action ->
      (∫ mode, test mode * collisionVector action mode ∂reference) =
        weakCollisionSlope collision test action
  signed_measure_representation : forall action,
    reference.withDensityᵥ (collisionVector action) =
      signedCollisionMeasure collision action

/-- Canonical bounded-action/test representation supplied by every finite
resonant three-wave measure. -/
def canonicalBoundedPointwiseCollisionRepresentation
    (collision : ResonantThreeWaveMeasure Mode) :
    BoundedPointwiseCollisionRepresentation collision where
  reference := collisionReferenceMeasure collision
  collisionVector := collisionVector collision
  measurable_output := measurable_collisionVector collision
  integrable_output := by
    intro test action htest _haction
    exact integrable_test_mul_collisionVector collision htest
  represents := by
    intro test action htest haction
    exact integral_test_mul_collisionVector_eq_weakCollisionSlope
      collision htest haction
  signed_measure_representation :=
    withDensity_collisionVector_eq_signedCollisionMeasure collision

/-- The RN-derived operator can be packaged as generic kinetic collision data;
its weak representation theorem remains the bounded-action/test theorem above. -/
def radonNikodymCollisionData
    {DiscreteMode : Type} [MeasurableSpace DiscreteMode]
    (collision : ResonantThreeWaveMeasure DiscreteMode) :
    CollisionData DiscreteMode where
  omega := collision.frequency
  collision := collisionVector collision

@[simp] theorem radonNikodymCollisionData_omega
    {DiscreteMode : Type} [MeasurableSpace DiscreteMode]
    (collision : ResonantThreeWaveMeasure DiscreteMode) (mode : DiscreteMode) :
    (radonNikodymCollisionData collision).omega mode = collision.frequency mode := by
  rfl

@[simp] theorem radonNikodymCollisionData_collision
    {DiscreteMode : Type} [MeasurableSpace DiscreteMode]
    (collision : ResonantThreeWaveMeasure DiscreteMode)
    (action : DiscreteMode -> Real) (mode : DiscreteMode) :
    (radonNikodymCollisionData collision).collision action mode =
      collisionVector collision action mode := by
  rfl

end

end ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
