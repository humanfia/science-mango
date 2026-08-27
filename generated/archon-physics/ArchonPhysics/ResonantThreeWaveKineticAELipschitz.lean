import ArchonPhysics.ResonantThreeWaveKineticAEBounded

/-!
# Almost-everywhere L-infinity Lipschitz bound for the RN collision vector

For two measurable actions in a common pointwise radius-`R` ball whose
pointwise distance is at most `epsilon`, the common triad flux difference is
bounded by `6 * R * epsilon`.  Transport through the three collision legs is
then dominated by that same constant times the sum of the three leg
marginals.  Hence the two RN collision vectors differ by at most
`6 * R * epsilon` almost everywhere in the canonical reference measure.

The conclusion is deliberately almost everywhere; no choice of totalized RN
representative is claimed to satisfy the inequality at every mode.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticAELipschitz

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticL1Stability
open scoped MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The variation of the common signed triad flux-difference measure is
dominated by the uniform flux-difference bound times collision measure. -/
theorem fluxDifferenceSignedTriadMeasure_variation_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon) :
    (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation <=
      ENNReal.ofReal (6 * radius * epsilon) •
        (collision.collisionMeasure : Measure (Fin 3 -> Mode)) := by
  have hbounded₁ : IsBoundedMeasurable action₁ :=
    ⟨haction₁_measurable, ⟨radius, haction₁⟩⟩
  have hbounded₂ : IsBoundedMeasurable action₂ :=
    ⟨haction₂_measurable, ⟨radius, haction₂⟩⟩
  have hflux := integrable_triadFlux_sub collision hbounded₁ hbounded₂
  rw [fluxDifferenceSignedTriadMeasure, Measure.variation_withDensityᵥ hflux,
    ← withDensity_const]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (fun triad => by
    change ‖triadFlux action₁ triad - triadFlux action₂ triad‖ₑ <=
      ENNReal.ofReal (6 * radius * epsilon)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (norm_triadFlux_sub_le_uniform hradius hepsilon
        haction₁ haction₂ hdistance triad))

/-- The same sharp constant dominates one transported leg difference. -/
theorem legFluxDifferenceSignedMeasure_variation_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon)
    (leg : Fin 3) :
    (legFluxDifferenceSignedMeasure collision action₁ action₂ leg).variation <=
      ENNReal.ofReal (6 * radius * epsilon) • legMarginal collision leg := by
  calc
    _ <= (fluxDifferenceSignedTriadMeasure collision action₁ action₂).variation.map
        (triadLeg leg) := VectorMeasure.variation_map_le
    _ <= (ENNReal.ofReal (6 * radius * epsilon) •
        (collision.collisionMeasure : Measure (Fin 3 -> Mode))).map (triadLeg leg) :=
      Measure.map_mono
        (fluxDifferenceSignedTriadMeasure_variation_le collision hradius hepsilon
          haction₁_measurable haction₂_measurable haction₁ haction₂ hdistance)
        (measurable_triadLeg leg)
    _ = _ := by
      rw [Measure.map_smul]
      rfl

/-- Net signed collision-difference variation is dominated by the same
constant times the full three-leg reference measure. -/
theorem signedCollisionDifferenceMeasure_variation_le_reference
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon) :
    (signedCollisionDifferenceMeasure collision action₁ action₂).variation <=
      ENNReal.ofReal (6 * radius * epsilon) • collisionReferenceMeasure collision := by
  let leg₀ := legFluxDifferenceSignedMeasure collision action₁ action₂ 0
  let leg₁ := legFluxDifferenceSignedMeasure collision action₁ action₂ 1
  let leg₂ := legFluxDifferenceSignedMeasure collision action₁ action₂ 2
  let K := ENNReal.ofReal (6 * radius * epsilon)
  have h₀₁ : (leg₀ - leg₁).variation <= leg₀.variation + leg₁.variation :=
    VectorMeasure.variation_sub_le
  have h₀₁₂ : ((leg₀ - leg₁) - leg₂).variation <=
      (leg₀ - leg₁).variation + leg₂.variation :=
    VectorMeasure.variation_sub_le
  have htotal : ((leg₀ - leg₁) - leg₂).variation <=
      (leg₀.variation + leg₁.variation) + leg₂.variation :=
    h₀₁₂.trans (add_le_add h₀₁ le_rfl)
  change ((leg₀ - leg₁) - leg₂).variation <= _
  calc
    _ <= (leg₀.variation + leg₁.variation) + leg₂.variation := htotal
    _ <= (K • legMarginal collision 0 + K • legMarginal collision 1) +
        K • legMarginal collision 2 := by
      apply add_le_add
      · apply add_le_add
        · exact legFluxDifferenceSignedMeasure_variation_le collision hradius hepsilon
            haction₁_measurable haction₂_measurable haction₁ haction₂ hdistance 0
        · exact legFluxDifferenceSignedMeasure_variation_le collision hradius hepsilon
            haction₁_measurable haction₂_measurable haction₁ haction₂ hdistance 1
      · exact legFluxDifferenceSignedMeasure_variation_le collision hradius hepsilon
          haction₁_measurable haction₂_measurable haction₁ haction₂ hdistance 2
    _ = K • collisionReferenceMeasure collision := by
      rw [collisionReferenceMeasure, smul_add, smul_add]

/-- Signed density of the pointwise collision-vector difference is exactly
the common-density signed collision-difference measure. -/
theorem withDensity_collisionVector_sub_eq_signedCollisionDifference
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    (collisionReferenceMeasure collision).withDensityᵥ
        (collisionVector collision action₁ - collisionVector collision action₂) =
      signedCollisionDifferenceMeasure collision action₁ action₂ := by
  rw [withDensityᵥ_sub
    (integrable_collisionVector collision action₁)
    (integrable_collisionVector collision action₂),
    withDensity_collisionVector_eq_signedCollisionMeasure,
    withDensity_collisionVector_eq_signedCollisionMeasure]
  exact (signedCollisionDifferenceMeasure_eq_sub collision haction₁ haction₂).symm

/-- Variation of the collision-vector difference density is exactly the net
signed collision-difference variation. -/
theorem withDensity_enorm_collisionVector_sub_eq_variation
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real}
    (haction₁ : IsBoundedMeasurable action₁)
    (haction₂ : IsBoundedMeasurable action₂) :
    (collisionReferenceMeasure collision).withDensity
        (fun mode => ‖collisionVector collision action₁ mode -
          collisionVector collision action₂ mode‖ₑ) =
      (signedCollisionDifferenceMeasure collision action₁ action₂).variation := by
  have hsub := (integrable_collisionVector collision action₁).sub
    (integrable_collisionVector collision action₂)
  change (collisionReferenceMeasure collision).withDensity
      (fun mode => ‖(collisionVector collision action₁ -
        collisionVector collision action₂) mode‖ₑ) = _
  rw [← Measure.variation_withDensityᵥ hsub,
    withDensity_collisionVector_sub_eq_signedCollisionDifference
      collision haction₁ haction₂]

/-- Measure-level domination of the collision-vector difference norm. -/
theorem withDensity_enorm_collisionVector_sub_le
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon) :
    (collisionReferenceMeasure collision).withDensity
        (fun mode => ‖collisionVector collision action₁ mode -
          collisionVector collision action₂ mode‖ₑ) <=
      ENNReal.ofReal (6 * radius * epsilon) •
        collisionReferenceMeasure collision := by
  have hbounded₁ : IsBoundedMeasurable action₁ :=
    ⟨haction₁_measurable, ⟨radius, haction₁⟩⟩
  have hbounded₂ : IsBoundedMeasurable action₂ :=
    ⟨haction₂_measurable, ⟨radius, haction₂⟩⟩
  rw [withDensity_enorm_collisionVector_sub_eq_variation
    collision hbounded₁ hbounded₂]
  exact signedCollisionDifferenceMeasure_variation_le_reference collision
    hradius hepsilon haction₁_measurable haction₂_measurable
    haction₁ haction₂ hdistance

/-- ENNReal form of the sharp a.e. collision-vector difference bound. -/
theorem collisionVector_sub_enorm_le_ae
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      ‖collisionVector collision action₁ mode -
        collisionVector collision action₂ mode‖ₑ <=
        ENNReal.ofReal (6 * radius * epsilon) := by
  have hmeasure := withDensity_enorm_collisionVector_sub_le collision
    hradius hepsilon haction₁_measurable haction₂_measurable
    haction₁ haction₂ hdistance
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    ((measurable_collisionVector collision action₁).sub
      (measurable_collisionVector collision action₂)).enorm
  intro s hs _
  rw [← withDensity_apply _ hs, ← withDensity_apply _ hs,
    withDensity_const]
  exact hmeasure s

/-- Real-norm form: uniformly close actions in a common radius ball have RN
collision vectors differing by at most `6 * radius * epsilon` almost
everywhere in the canonical reference measure. -/
theorem collisionVector_sub_norm_le_ae
    (collision : ResonantThreeWaveMeasure Mode)
    {action₁ action₂ : Mode -> Real} {radius epsilon : Real}
    (hradius : 0 <= radius) (hepsilon : 0 <= epsilon)
    (haction₁_measurable : Measurable action₁)
    (haction₂_measurable : Measurable action₂)
    (haction₁ : forall mode, norm (action₁ mode) <= radius)
    (haction₂ : forall mode, norm (action₂ mode) <= radius)
    (hdistance : forall mode,
      norm (action₁ mode - action₂ mode) <= epsilon) :
    ∀ᵐ mode ∂collisionReferenceMeasure collision,
      norm (collisionVector collision action₁ mode -
        collisionVector collision action₂ mode) <=
        6 * radius * epsilon := by
  have hK : 0 <= 6 * radius * epsilon := by positivity
  filter_upwards [collisionVector_sub_enorm_le_ae collision
    hradius hepsilon haction₁_measurable haction₂_measurable
    haction₁ haction₂ hdistance] with mode hmode
  rw [← ofReal_norm] at hmode
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hmode

end

end ArchonPhysics.ResonantThreeWaveKineticAELipschitz
