import ArchonPhysics.AdditiveTriangleMeasureSupport
import ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
import ArchonPhysics.ResonantThreeWaveKineticEquilibrium
import ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

namespace ArchonPhysics.AcousticRayleighJeansLInfinityObstruction

open Filter MeasureTheory Metric Set
open ArchonPhysics.AdditiveTriangleMeasureSupport
open ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory Topology

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

def HasAcousticMassAtZero (mu : Measure Mode) (frequency : Mode -> Real) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    mu {mode | 0 < frequency mode ∧ frequency mode < epsilon} ≠ 0

theorem not_memLp_top_rayleighJeansAction_of_hasAcousticMassAtZero
    (mu : Measure Mode) (frequency : Mode -> Real)
    (hacoustic : HasAcousticMassAtZero mu frequency)
    {temperature : Real} (htemperature : 0 < temperature) :
    ¬ MemLp (rayleighJeansAction temperature frequency) ∞ mu := by
  intro hmem
  let bound : Real := lpNorm
    (rayleighJeansAction temperature frequency) ∞ mu
  have hbound_nonnegative : 0 <= bound := lpNorm_nonneg
  let epsilon : Real := temperature / (bound + 1)
  have hepsilon : 0 < epsilon := by
    exact div_pos htemperature (by linarith)
  have hacoustic_ne :
      mu {mode | 0 < frequency mode ∧ frequency mode < epsilon} ≠ 0 :=
    hacoustic epsilon hepsilon
  have haeBound : ∀ᵐ mode ∂mu,
      ‖rayleighJeansAction temperature frequency mode‖ <= bound := by
    simpa only [bound] using ae_le_lpNorm_exponent_top hmem
  have hbadZero : mu {mode |
      ¬ ‖rayleighJeansAction temperature frequency mode‖ <= bound} = 0 :=
    ae_iff.mp haeBound
  have hsubset : {mode | 0 < frequency mode ∧ frequency mode < epsilon} ⊆
      {mode | ¬ ‖rayleighJeansAction temperature frequency mode‖ <= bound} := by
    intro mode hmode
    have hscaled : frequency mode * (bound + 1) < temperature := by
      exact (lt_div_iff₀ (by linarith : 0 < bound + 1)).mp hmode.2
    have hratio : bound < temperature / frequency mode := by
      apply (lt_div_iff₀ hmode.1).mpr
      nlinarith
    change ¬ ‖temperature / frequency mode‖ <= bound
    rw [Real.norm_eq_abs, abs_of_pos (div_pos htemperature hmode.1)]
    exact not_le_of_gt hratio
  exact hacoustic_ne (measure_mono_null hsubset hbadZero)

theorem hasAcousticMassAtZero_map_fst_of_triangle_dominance
    {W : Real} (hW : 0 < W) (pairMeasure : Measure (Real × Real))
    (hlower :
      volume.restrict (additiveFrequencyTriangle W) ≪
        pairMeasure.restrict (additiveFrequencyTriangle W)) :
    HasAcousticMassAtZero (Measure.map Prod.fst pairMeasure) id := by
  intro epsilon hepsilon
  let radius : Real := min epsilon W / 4
  have hradius : 0 < radius :=
    div_pos (lt_min hepsilon hW) (by norm_num)
  have hradius_epsilon : radius < epsilon := by
    dsimp only [radius]
    have hmin := min_le_left epsilon W
    nlinarith
  have hradius_W : radius + radius < W := by
    dsimp only [radius]
    have hmin := min_le_right epsilon W
    nlinarith
  let point : Real × Real := (radius, radius)
  have hpointTriangle : point ∈ additiveFrequencyTriangle W :=
    ⟨hradius.le, hradius.le, hradius_W.le⟩
  have hpointSupport :
      point ∈ (pairMeasure.restrict (additiveFrequencyTriangle W)).support :=
    (fullSupport_of_volume_absolutelyContinuous hW hlower) hpointTriangle
  let neighborhood : Set (Real × Real) := Prod.fst ⁻¹' Ioo 0 epsilon
  have hpointNeighborhood : point ∈ neighborhood :=
    ⟨hradius, hradius_epsilon⟩
  have hneighborhoodOpen : IsOpen neighborhood :=
    isOpen_Ioo.preimage continuous_fst
  have hpositiveRestricted :
      0 < pairMeasure.restrict (additiveFrequencyTriangle W) neighborhood :=
    (Measure.mem_support_iff_forall point).mp hpointSupport neighborhood
      (hneighborhoodOpen.mem_nhds hpointNeighborhood)
  have hpositive : 0 < pairMeasure neighborhood :=
    hpositiveRestricted.trans_le (Measure.restrict_le_self neighborhood)
  have hmap :
      Measure.map Prod.fst pairMeasure (Ioo 0 epsilon) =
        pairMeasure neighborhood := by
    rw [Measure.map_apply measurable_fst measurableSet_Ioo]
  rw [show {omega : Real | 0 < id omega ∧ id omega < epsilon} =
      Ioo 0 epsilon by rfl, hmap]
  exact ne_of_gt hpositive

theorem map_fst_childFrequencyPairMeasure_eq_map_frequency_legMarginal_one
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode) :
    Measure.map Prod.fst (childFrequencyPairMeasure collision) =
      Measure.map collision.frequency (legMarginal collision 1) := by
  unfold childFrequencyPairMeasure legMarginal
  rw [Measure.map_map measurable_fst
      (measurable_childFrequencyPair collision),
    Measure.map_map collision.measurable_frequency
      (measurable_triadLeg 1)]
  rfl

theorem hasAcousticMassAtZero_collisionReference_of_childTriangleDominance
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    {W : Real} (hW : 0 < W)
    (hlower :
      volume.restrict (additiveFrequencyTriangle W) ≪
        (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W)) :
    HasAcousticMassAtZero (collisionReferenceMeasure collision)
      collision.frequency := by
  have hpair :=
    hasAcousticMassAtZero_map_fst_of_triangle_dominance hW
      (childFrequencyPairMeasure collision) hlower
  intro epsilon hepsilon
  have hsmallPair :
      Measure.map Prod.fst (childFrequencyPairMeasure collision)
          (Ioo 0 epsilon) ≠ 0 := by
    rw [← show {omega : Real | 0 < omega ∧ omega < epsilon} =
      Ioo 0 epsilon by rfl]
    exact hpair epsilon hepsilon
  rw [map_fst_childFrequencyPairMeasure_eq_map_frequency_legMarginal_one]
      at hsmallPair
  have hsmallLeg :
      legMarginal collision 1
        {mode | 0 < collision.frequency mode ∧
          collision.frequency mode < epsilon} ≠ 0 := by
    rw [Measure.map_apply collision.measurable_frequency measurableSet_Ioo]
      at hsmallPair
    simpa only [Set.preimage, Set.mem_Ioo] using hsmallPair
  intro hrefZero
  apply hsmallLeg
  apply bot_unique
  calc
    legMarginal collision 1
        {mode | 0 < collision.frequency mode ∧
          collision.frequency mode < epsilon} <=
      collisionReferenceMeasure collision
        {mode | 0 < collision.frequency mode ∧
          collision.frequency mode < epsilon} :=
      legMarginal_le_collisionReferenceMeasure collision 1 _
    _ = 0 := hrefZero

theorem not_memLp_top_rayleighJeansAction_of_childTriangleDominance
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    {W : Real} (hW : 0 < W)
    (hlower :
      volume.restrict (additiveFrequencyTriangle W) ≪
        (childFrequencyPairMeasure collision).restrict
          (additiveFrequencyTriangle W))
    {temperature : Real} (htemperature : 0 < temperature) :
    ¬ MemLp
      (rayleighJeansAction temperature collision.frequency) ∞
      (collisionReferenceMeasure collision) :=
  not_memLp_top_rayleighJeansAction_of_hasAcousticMassAtZero
    (collisionReferenceMeasure collision) collision.frequency
    (hasAcousticMassAtZero_collisionReference_of_childTriangleDominance
      collision hW hlower)
    htemperature

theorem scale_eq_zero_of_frequencyInverse_memLp_top_of_hasAcousticMassAtZero
    (mu : Measure Mode) (frequency : Mode -> Real)
    (hacoustic : HasAcousticMassAtZero mu frequency)
    (action : Lp Real ∞ mu) (scale : Real)
    (hequilibrium : ∀ᵐ mode ∂mu,
      (action mode)⁻¹ = scale * frequency mode) :
    scale = 0 := by
  by_contra hscale
  let bound : Real := ‖action‖
  have hbound_nonnegative : 0 <= bound := norm_nonneg action
  let epsilon : Real :=
    1 / ((bound + 1) * (|scale| + 1))
  have hboundOne : 0 < bound + 1 := by linarith
  have hscaleOne : 0 < |scale| + 1 := by positivity
  have hdenominator : 0 < (bound + 1) * (|scale| + 1) :=
    mul_pos hboundOne hscaleOne
  have hepsilon : 0 < epsilon := one_div_pos.mpr hdenominator
  have hacoustic_ne :
      mu {mode | 0 < frequency mode ∧ frequency mode < epsilon} ≠ 0 :=
    hacoustic epsilon hepsilon
  have hnormBound : ∀ᵐ mode ∂mu, ‖action mode‖ <= bound := by
    simpa only [bound, Lp.norm_def,
      toReal_eLpNorm (Lp.aestronglyMeasurable action)] using
      ae_le_lpNorm_exponent_top (Lp.memLp action)
  have hgood : ∀ᵐ mode ∂mu,
      ‖action mode‖ <= bound ∧
        (action mode)⁻¹ = scale * frequency mode :=
    hnormBound.and hequilibrium
  have hbadZero : mu {mode |
      ¬ (‖action mode‖ <= bound ∧
        (action mode)⁻¹ = scale * frequency mode)} = 0 :=
    ae_iff.mp hgood
  have hsubset :
      {mode | 0 < frequency mode ∧ frequency mode < epsilon} ⊆
        {mode | ¬ (‖action mode‖ <= bound ∧
          (action mode)⁻¹ = scale * frequency mode)} := by
    intro mode hmode hmodeGood
    have hrhsNe : scale * frequency mode ≠ 0 :=
      mul_ne_zero hscale (ne_of_gt hmode.1)
    have hactionNe : action mode ≠ 0 := by
      intro hzero
      rw [hzero, inv_zero] at hmodeGood
      exact hrhsNe hmodeGood.2.symm
    have habsActionPos : 0 < |action mode| :=
      abs_pos.mpr hactionNe
    have habsActionUpper : |action mode| < bound + 1 := by
      rw [← Real.norm_eq_abs]
      exact hmodeGood.1.trans_lt (lt_add_one bound)
    have hinverseLower : 1 / (bound + 1) < |(action mode)⁻¹| := by
      rw [abs_inv]
      simpa only [one_div] using
        one_div_lt_one_div_of_lt habsActionPos habsActionUpper
    have hsmallScaled :
        |scale| * frequency mode < 1 / (bound + 1) := by
      apply (lt_div_iff₀ hboundOne).mpr
      have hfrequencyScaled :
          frequency mode * ((bound + 1) * (|scale| + 1)) < 1 :=
        (lt_div_iff₀ hdenominator).mp hmode.2
      calc
        |scale| * frequency mode * (bound + 1) <
            (|scale| + 1) * frequency mode * (bound + 1) := by
          gcongr
          · exact hmode.1
          · exact lt_add_one _
        _ = frequency mode * ((bound + 1) * (|scale| + 1)) := by ring
        _ < 1 := hfrequencyScaled
    have habsEquilibrium :
        |(action mode)⁻¹| = |scale| * frequency mode := by
      rw [hmodeGood.2, abs_mul, abs_of_pos hmode.1]
    rw [habsEquilibrium] at hinverseLower
    exact (not_lt_of_ge hinverseLower.le) hsmallScaled
  exact hacoustic_ne (measure_mono_null hsubset hbadZero)

theorem action_eq_zero_of_frequencyInverse_of_hasAcousticMassAtZero
    (mu : Measure Mode) (frequency : Mode -> Real)
    (hacoustic : HasAcousticMassAtZero mu frequency)
    (action : Lp Real ∞ mu) (scale : Real)
    (hequilibrium : ∀ᵐ mode ∂mu,
      (action mode)⁻¹ = scale * frequency mode) :
    action = 0 := by
  have hscale :=
    scale_eq_zero_of_frequencyInverse_memLp_top_of_hasAcousticMassAtZero
      mu frequency hacoustic action scale hequilibrium
  apply Lp.ext
  filter_upwards [hequilibrium, Lp.coeFn_zero Real ∞ mu]
    with mode hmode hzero
  rw [hscale, zero_mul] at hmode
  have hactionZero : action mode = 0 := inv_eq_zero.mp hmode
  have hzero' : (0 : Lp Real ∞ mu) mode = 0 := by
    simpa only [Pi.zero_apply] using hzero
  exact hactionZero.trans hzero'.symm

theorem rayleighJeansEquilibriumSet_eq_singleton_zero_of_hasAcousticMassAtZero
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    (hacoustic : HasAcousticMassAtZero
      (collisionReferenceMeasure collision) collision.frequency) :
    rayleighJeansEquilibriumSet collision = {0} := by
  ext action
  constructor
  · rintro ⟨scale, hequilibrium⟩
    exact Set.mem_singleton_iff.mpr
      (action_eq_zero_of_frequencyInverse_of_hasAcousticMassAtZero
        (collisionReferenceMeasure collision) collision.frequency
        hacoustic action scale hequilibrium)
  · intro haction
    rw [Set.mem_singleton_iff] at haction
    subst action
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero Real ∞
      (collisionReferenceMeasure collision)] with mode hzero
    have hzero' : (0 : CanonicalLInfinity collision) mode = 0 := by
      simpa only [Pi.zero_apply] using hzero
    simp only [hzero', inv_zero, zero_mul]

theorem rayleighJeansDistance_eq_norm_of_hasAcousticMassAtZero
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    (hacoustic : HasAcousticMassAtZero
      (collisionReferenceMeasure collision) collision.frequency)
    (action : CanonicalLInfinity collision) :
    rayleighJeansDistance collision action = ‖action‖ := by
  rw [rayleighJeansDistance,
    rayleighJeansEquilibriumSet_eq_singleton_zero_of_hasAcousticMassAtZero
      collision hacoustic,
    infDist_singleton, dist_zero_right]

theorem floor_le_norm_of_aeLowerBound_of_hasAcousticMassAtZero
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    (hacoustic : HasAcousticMassAtZero
      (collisionReferenceMeasure collision) collision.frequency)
    {floor : Real} (action : CanonicalLInfinity collision)
    (hactionFloor : ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation.AELowerBound
      collision floor action) :
    floor <= ‖action‖ := by
  have hmeasureNe : collisionReferenceMeasure collision ≠ 0 := by
    intro hzero
    have hone := hacoustic 1 zero_lt_one
    rw [hzero] at hone
    simp at hone
  let _ : NeZero (collisionReferenceMeasure collision) := ⟨hmeasureNe⟩
  have hnormBound : ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖action mode‖ <= ‖action‖ := by
    simpa only [Lp.norm_def,
      toReal_eLpNorm (Lp.aestronglyMeasurable action)] using
      ae_le_lpNorm_exponent_top (Lp.memLp action)
  obtain ⟨mode, hfloorMode, hnormMode⟩ :=
    (hactionFloor.and hnormBound).exists
  calc
    floor <= action mode := hfloorMode
    _ <= ‖action mode‖ := Real.le_norm_self _
    _ <= ‖action‖ := hnormMode

theorem floor_le_rayleighJeansDistance_of_hasAcousticMassAtZero
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    (hacoustic : HasAcousticMassAtZero
      (collisionReferenceMeasure collision) collision.frequency)
    {floor : Real} (action : CanonicalLInfinity collision)
    (hactionFloor : ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation.AELowerBound
      collision floor action) :
    floor <= rayleighJeansDistance collision action := by
  rw [rayleighJeansDistance_eq_norm_of_hasAcousticMassAtZero
    collision hacoustic]
  exact floor_le_norm_of_aeLowerBound_of_hasAcousticMassAtZero
    collision hacoustic action hactionFloor

theorem not_tendsto_rayleighJeansDistance_zero_of_uniformPositiveBuffer
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    (hacoustic : HasAcousticMassAtZero
      (collisionReferenceMeasure collision) collision.frequency)
    {floor : Real} (hfloor : 0 < floor)
    (trajectory : Real -> CanonicalLInfinity collision)
    (hactionFloor : forall t, 0 <= t ->
      AELowerBound collision floor (trajectory t)) :
    ¬ Tendsto
      (fun t => rayleighJeansDistance collision (trajectory t))
      atTop (nhds 0) := by
  intro hrelax
  have hsmall : ∀ᶠ t in atTop,
      rayleighJeansDistance collision (trajectory t) < floor :=
    hrelax.eventually (Iio_mem_nhds hfloor)
  obtain ⟨t, htSmall, ht⟩ :=
    (hsmall.and (eventually_ge_atTop (0 : Real))).exists
  exact (not_lt_of_ge
    (floor_le_rayleighJeansDistance_of_hasAcousticMassAtZero
      collision hacoustic (trajectory t) (hactionFloor t ht))) htSmall

theorem not_tendsto_rayleighJeansDistance_zero_of_childTriangleDominance_uniformPositiveBuffer
    (collision : ArchonPhysics.ResonantThreeWaveMeasure Mode)
    {W : Real} (hW : 0 < W)
    (hlower :
      volume.restrict
          (ArchonPhysics.ContinuousThreeWaveBalanceRigidity.additiveFrequencyTriangle W) ≪
        (ArchonPhysics.ContinuousThreeWaveBalanceRigidity.childFrequencyPairMeasure
          collision).restrict
          (ArchonPhysics.ContinuousThreeWaveBalanceRigidity.additiveFrequencyTriangle W))
    {floor : Real} (hfloor : 0 < floor)
    (trajectory : Real -> CanonicalLInfinity collision)
    (hactionFloor : forall t, 0 <= t ->
      AELowerBound collision floor (trajectory t)) :
    ¬ Tendsto
      (fun t => rayleighJeansDistance collision (trajectory t))
      atTop (nhds 0) :=
  not_tendsto_rayleighJeansDistance_zero_of_uniformPositiveBuffer
    collision
    (hasAcousticMassAtZero_collisionReference_of_childTriangleDominance
      collision hW hlower)
    hfloor trajectory hactionFloor

end

end ArchonPhysics.AcousticRayleighJeansLInfinityObstruction
