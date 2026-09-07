import Family8Grounding.Family8ThinPlankFiveParameterMidpointDirectionPackingV3
import Family8Grounding.Family8ContractedJohnActualTubeProxyV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ContractedJohnProxyFiveParameterPackingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnActualTubeProxyV2
open Family8ThinPlankEssentialDistinctPackingV4
open Family8ThinPlankFiveParameterPackingV2
open Family8ThinPlankFiveParameterMidpointDirectionPackingV3
open Family8TubeJohnContractedLipschitzV1

noncomputable section

/-!
# Contracted-John proxy data for the five-parameter packing kernel

The proxy axis is a unit extension, so no containment of that axis in the
contracted parent is asserted.  Instead, the normalized direction is obtained
from the real affine image vector.  An explicit lower scale `ell` converts raw
vector coordinate bounds into normalized-direction bounds.
-/

/-- The midpoint of the proxy unit extension is exactly the midpoint of the
two real affine-image endpoints. -/
theorem tubeAxisMidpoint_contractedJohnProxyTube
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) :
    tubeAxisMidpoint (contractedJohnProxyTube P hrho w T) =
      affineImageAxisCenter (contractedTubeJohnAffineEquiv P hrho w) T := by
  unfold tubeAxisMidpoint contractedJohnProxyTube affineImageUnitExtensionAxis
  simp only
  module

/-- A raw affine-vector coordinate bound at a lower length scale becomes a
bound for the normalized proxy direction. -/
theorem abs_inner_affineImageAxisDirection_le_of_lower_length
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta)
    (u : Space) (ell s : Real)
    (hellNorm : ell ≤ ‖affineImageAxisVector e T‖)
    (hs : 0 ≤ s)
    (hcoord : |⟪u, affineImageAxisVector e T⟫_Real| ≤ ell * s) :
    |⟪u, affineImageAxisDirection e T⟫_Real| ≤ s := by
  let v := affineImageAxisVector e T
  have hvne : v ≠ 0 := affineImageAxisVector_ne_zero e T
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  change |⟪u, ‖v‖⁻¹ • v⟫_Real| ≤ s
  rw [real_inner_smul_right, abs_mul,
    abs_of_pos (inv_pos.mpr hvpos)]
  calc
    ‖v‖⁻¹ * |⟪u, v⟫_Real| ≤ ‖v‖⁻¹ * (ell * s) := by
      gcongr
    _ ≤ ‖v‖⁻¹ * (‖v‖ * s) := by
      gcongr
    _ = (‖v‖⁻¹ * ‖v‖) * s := by ring
    _ = s := by rw [inv_mul_cancel₀ hvpos.ne', one_mul]

/-- Same-parent contracted proxy tubes satisfy the quadratic count bound once
the real image midpoints and raw image vectors obey the two plank-coordinate
bounds.  Pairwise distinctness is required for the actual proxy tubes; it is
not silently imported from the source family. -/
theorem card_le_contractedJohnProxy_fiveParameterCap
    {delta rho : NNReal} {parameter : Type} [Fintype parameter]
    [DecidableEq parameter]
    (P : Tube rho) (hrho : 0 < rho) (w : JohnAxisWitness P.body)
    (source : parameter → Tube delta)
    (hdeltaPos : 0 < delta)
    (hsourceParent : ∀ p, (source p).carrier ⊆ P.carrier)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (R : Real) (hR : 0 ≤ R)
    (ell : parameter → Real)
    (hellNorm : ∀ p,
      ell p ≤ ‖affineImageAxisVector
        (contractedTubeJohnAffineEquiv P hrho w) (source p)‖)
    (hcenter0 : ∀ p,
      |⟪frame 0,
        affineImageAxisCenter
          (contractedTubeJohnAffineEquiv P hrho w) (source p)⟫_Real| ≤
        (contractedJohnProxyRadius delta rho : Real) / 2)
    (hcenter1 : ∀ p,
      |⟪frame 1,
        affineImageAxisCenter
          (contractedTubeJohnAffineEquiv P hrho w) (source p)⟫_Real| ≤
        (R * (contractedJohnProxyRadius delta rho : Real)) / 2)
    (hvector0 : ∀ p,
      |⟪frame 0,
        affineImageAxisVector
          (contractedTubeJohnAffineEquiv P hrho w) (source p)⟫_Real| ≤
        ell p * (contractedJohnProxyRadius delta rho : Real))
    (hvector1 : ∀ p,
      |⟪frame 1,
        affineImageAxisVector
          (contractedTubeJohnAffineEquiv P hrho w) (source p)⟫_Real| ≤
        ell p * (R * (contractedJohnProxyRadius delta rho : Real)))
    (hproxySmall :
      contractedJohnProxyRadius delta rho ≤ (1 / 100 : NNReal))
    (hthin :
      (contractedJohnProxyRadius delta rho : Real) ^ 2 +
        (R * (contractedJohnProxyRadius delta rho : Real)) ^ 2 ≤
          (3 : Real) / 4)
    (hpairwise : Set.Pairwise (Set.univ : Set parameter) fun p q =>
      EssentiallyDistinct
        (contractedJohnProxyTube P hrho w (source p))
        (contractedJohnProxyTube P hrho w (source q))) :
    Fintype.card parameter ≤ thinPlankFivePackingNatCap (3 * R) := by
  let proxy : parameter → Tube (contractedJohnProxyRadius delta rho) :=
    fun p => contractedJohnProxyTube P hrho w (source p)
  have hproxyPos : 0 < contractedJohnProxyRadius delta rho :=
    contractedJohnProxyRadius_pos hdeltaPos hrho
  have hmidNorm (p : parameter) :
      ‖tubeAxisMidpoint (proxy p) - (0 : Space)‖ ≤ 2 := by
    rw [sub_zero]
    change ‖tubeAxisMidpoint
      (contractedJohnProxyTube P hrho w (source p))‖ ≤ 2
    rw [tubeAxisMidpoint_contractedJohnProxyTube]
    exact (norm_affineImageAxisCenter_contracted_le_eighth
      P hrho w (source p) (hsourceParent p)).trans (by norm_num)
  have hmid0 (p : parameter) :
      |⟪frame 0, tubeAxisMidpoint (proxy p) - (0 : Space)⟫_Real| ≤
        (contractedJohnProxyRadius delta rho : Real) / 2 := by
    simp only [sub_zero]
    rw [show tubeAxisMidpoint (proxy p) =
        affineImageAxisCenter
          (contractedTubeJohnAffineEquiv P hrho w) (source p) by
      exact tubeAxisMidpoint_contractedJohnProxyTube P hrho w (source p)]
    exact hcenter0 p
  have hmid1 (p : parameter) :
      |⟪frame 1, tubeAxisMidpoint (proxy p) - (0 : Space)⟫_Real| ≤
        (R * (contractedJohnProxyRadius delta rho : Real)) / 2 := by
    simp only [sub_zero]
    rw [show tubeAxisMidpoint (proxy p) =
        affineImageAxisCenter
          (contractedTubeJohnAffineEquiv P hrho w) (source p) by
      exact tubeAxisMidpoint_contractedJohnProxyTube P hrho w (source p)]
    exact hcenter1 p
  have hdir0 (p : parameter) :
      |⟪frame 0, (proxy p).axis.direction⟫_Real| ≤
        (contractedJohnProxyRadius delta rho : Real) := by
    change |⟪frame 0,
      affineImageAxisDirection
        (contractedTubeJohnAffineEquiv P hrho w) (source p)⟫_Real| ≤ _
    exact abs_inner_affineImageAxisDirection_le_of_lower_length
      _ _ _ (ell p) _ (hellNorm p) NNReal.zero_le_coe (hvector0 p)
  have hdir1 (p : parameter) :
      |⟪frame 1, (proxy p).axis.direction⟫_Real| ≤
        R * (contractedJohnProxyRadius delta rho : Real) := by
    change |⟪frame 1,
      affineImageAxisDirection
        (contractedTubeJohnAffineEquiv P hrho w) (source p)⟫_Real| ≤ _
    exact abs_inner_affineImageAxisDirection_le_of_lower_length
      _ _ _ (ell p) _ (hellNorm p)
        (mul_nonneg hR NNReal.zero_le_coe) (hvector1 p)
  exact card_le_thinPlankFivePackingNatCap_of_midpoint_direction_bounds
    frame 0 proxy R hproxyPos hproxySmall hR hmidNorm hmid0 hmid1
      hdir0 hdir1 hthin hpairwise

#print axioms tubeAxisMidpoint_contractedJohnProxyTube
#print axioms abs_inner_affineImageAxisDirection_le_of_lower_length
#print axioms card_le_contractedJohnProxy_fiveParameterCap

end
end Family8ContractedJohnProxyFiveParameterPackingV2
