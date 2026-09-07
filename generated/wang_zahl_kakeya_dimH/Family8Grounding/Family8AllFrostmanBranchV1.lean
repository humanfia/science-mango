import Family8Grounding.Family8AllFrostmanBranchNumericsV1

open scoped ENNReal NNReal
open MeasureTheory

namespace Family8AllFrostmanBranchV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanUnionMultiplicityAlgebraV1
open Family8AllFrostmanBranchNumericsV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Closing the all-Frostman branch of Main Lemma 1

This is the exact final implication used in the paper's all-Frostman case.
The two geometric inputs remain visible: a constant-factor packing estimate
for the summed tube volume and the union-volume lower bound produced by the
Sticky theorem.  Everything after those inputs, including absorption of the
packing constant and conversion to average multiplicity, is proved here.
-/

/-- A Sticky union-volume lower bound at exponent `gamma / 2`, together with
the actual constant-factor packing estimate, gives the exact `K_F(gamma / 2)`
average-multiplicity conclusion. -/
theorem averageMultiplicity_le_frostmanRHS_of_allFrostman_branch
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) {C : ENNReal}
    {epsilon gamma : Real}
    (hdelta : 0 < delta)
    (hdeltaThreshold :
      delta <= allFrostmanConstantThreshold C epsilon gamma)
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon)
    (hgamma0 : 0 <= gamma) (hgamma4 : gamma <= 4)
    (hvolume :
      D.actualFamilyVolume <= C * (delta : ENNReal) ^ (-2 : Real))
    (hunion :
      (delta : ENNReal) ^ (gamma / 2) <=
        volume D.shading.shadedUnion) :
    D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon
        (gamma / 2) := by
  have hbeta0 : 0 <= gamma / 2 := by linarith
  have hbeta2 : gamma / 2 <= 2 := by linarith
  have hrequired :
      frostmanUnionLowerRHS delta D.actualFamilyVolume epsilon
          (gamma / 2) <= volume D.shading.shadedUnion :=
    (frostmanUnionLowerRHS_halfExponent_le_of_volume_constant
      hdelta hdeltaThreshold hCtop hepsilon hgamma0 hvolume).trans hunion
  exact averageMultiplicity_le_frostmanMultiplicityRHS_of_unionLower
    D.shading hdelta hbeta0 hbeta2 hrequired

#print axioms averageMultiplicity_le_frostmanRHS_of_allFrostman_branch

end

end Family8AllFrostmanBranchV1
