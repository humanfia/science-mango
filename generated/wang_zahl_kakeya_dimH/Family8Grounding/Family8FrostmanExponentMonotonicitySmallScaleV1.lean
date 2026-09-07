import Family8Grounding.Family8FrostmanExponentMonotonicityV1

open scoped ENNReal NNReal

namespace Family8FrostmanExponentMonotonicitySmallScaleV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanExponentMonotonicityV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Frostman exponent monotonicity from a small-scale packing theorem

The actual common-point packing theorem is valid below a fixed geometric
scale (currently `1/100`), rather than for every admissible radius.  This is
the honest small-scale form of the exponent transport theorem: its terminal
scale is the minimum of the source property scale, the packing validity
scale, and the finite-constant absorption threshold.

The global theorem in `Family8FrostmanExponentMonotonicityV1` remains
available as the specialization in which the volume estimate has no scale
restriction.
-/

/-- A family-volume estimate valid only below `packingDelta0` is enough to
make `FrostmanProperty` monotone in its exponent. -/
theorem frostmanProperty_mono_of_familyVolumePackingAtSmallScales
    (K : ENNReal) (hKtop : K ≠ ∞)
    (packingDelta0 : NNReal) (hpackingDelta0 : 0 < packingDelta0)
    (hvolume :
      ∀ {delta : NNReal} {index : Type}
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index),
        D.IsAdmissible → delta ≤ packingDelta0 →
          D.actualFamilyVolume ≤
            K * (delta : ENNReal) ^ (-2 : Real))
    {lower upper : Real} (hlowerUpper : lower ≤ upper)
    (hlower : FrostmanProperty lower) :
    FrostmanProperty upper := by
  intro epsilon hepsilon
  have hhalfEpsilon : 0 < epsilon / 2 := by positivity
  obtain ⟨eta, sourceDelta0, heta, hsourceDelta0, hsourceHalf, hsource⟩ :=
    hlower.exists_parameters hhalfEpsilon
  let threshold : NNReal :=
    frostmanExponentTransportThreshold K epsilon lower upper
  let delta1 : NNReal :=
    min sourceDelta0 (min packingDelta0 threshold)
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    exact frostmanExponentTransportThreshold_pos K epsilon lower upper
  have hdelta1 : 0 < delta1 := by
    dsimp only [delta1]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨hsourceDelta0, hpackingDelta0, hthreshold⟩
  have hdelta1Half : delta1 ≤ (2 : NNReal)⁻¹ :=
    (min_le_left sourceDelta0 (min packingDelta0 threshold)).trans hsourceHalf
  refine ⟨eta, delta1, heta, hdelta1, hdelta1Half, ?_⟩
  intro delta index _ _ D hD hdelta hF
  have hdeltaSource : delta ≤ sourceDelta0 :=
    hdelta.trans (min_le_left sourceDelta0 (min packingDelta0 threshold))
  have hdeltaPacking : delta ≤ packingDelta0 :=
    hdelta.trans ((min_le_right sourceDelta0
      (min packingDelta0 threshold)).trans (min_le_left _ _))
  have hdeltaThreshold : delta ≤ threshold :=
    hdelta.trans ((min_le_right sourceDelta0
      (min packingDelta0 threshold)).trans (min_le_right _ _))
  have hlowerBound :
      D.shading.averageMultiplicity ≤
        frostmanMultiplicityRHS delta D.actualFamilyVolume
          (epsilon / 2) lower :=
    hsource delta index D hD hdeltaSource hF
  have hnumeric :
      frostmanMultiplicityRHS delta D.actualFamilyVolume
          (epsilon / 2) lower ≤
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon upper := by
    apply frostmanMultiplicityRHS_lower_le_upper_of_volumePacking
      hD.delta_pos
      (hD.delta_le_half.trans (by norm_num))
      (by simpa only [threshold] using hdeltaThreshold)
      hKtop hepsilon hlowerUpper
    exact hvolume D hD hdeltaPacking
  exact hlowerBound.trans hnumeric

#print axioms frostmanProperty_mono_of_familyVolumePackingAtSmallScales

end

end Family8FrostmanExponentMonotonicitySmallScaleV1
