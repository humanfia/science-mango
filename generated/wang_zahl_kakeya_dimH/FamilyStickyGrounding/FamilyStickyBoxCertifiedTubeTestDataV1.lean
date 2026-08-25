import FamilyStickyGrounding.FamilyStickyActualTubeTestDataV1
import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap

open Set
open scoped NNReal

namespace FamilyStickyBoxCertifiedTubeTestDataV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTestDataV1

noncomputable section

/-!
# Data-bearing box-certified tube/test input

The final random-motion wrapper consumes actual `BoxDimensionsCertificate`
data.  `HasBoxDimensions` and the outer `FrameBox` used by the incidence proof
are then produced internally, rather than accepted as theorem callbacks.
-/

structure BoxCertifiedTubeTestData
    (delta : NNReal) (tubeIndex : Type*) [DecidableEq tubeIndex] where
  data : ActualTubeTestData delta tubeIndex
  Cbox : NNReal
  side : Fin data.testCard -> Fin 3 -> NNReal
  certificate : forall K,
    BoxDimensionsCertificate Cbox (side K) (data.testBody K)

namespace BoxCertifiedTubeTestData

variable {delta : NNReal} {tubeIndex : Type*} [DecidableEq tubeIndex]

theorem certificate_hasBoxDimensions
    {C : NNReal} {side : Fin 3 -> NNReal} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) :
    HasBoxDimensions C side K :=
  ⟨cert.one_le, cert.box, cert.side_eq, cert.inner_le, cert.outer_le⟩

theorem hasBoxDimensions
    (B : BoxCertifiedTubeTestData delta tubeIndex) :
    forall K, HasBoxDimensions B.Cbox (B.side K) (B.data.testBody K) :=
  fun K => certificate_hasBoxDimensions (B.certificate K)

/-- Literal outer frame box carried by the input certificate. -/
def outerFrameBox
    (B : BoxCertifiedTubeTestData delta tubeIndex)
    (K : Fin B.data.testCard) : FrameBox :=
  (B.certificate K).box

theorem testBody_subset_outerFrameBox
    (B : BoxCertifiedTubeTestData delta tubeIndex)
    (K : Fin B.data.testCard) :
    (B.data.testBody K : Set Space) ⊆ (B.outerFrameBox K).carrier :=
  (B.certificate K).outer_le

theorem outerFrameBox_side
    (B : BoxCertifiedTubeTestData delta tubeIndex)
    (K : Fin B.data.testCard) :
    (B.outerFrameBox K).side = B.side K :=
  (B.certificate K).side_eq

#print axioms certificate_hasBoxDimensions
#print axioms hasBoxDimensions
#print axioms testBody_subset_outerFrameBox
#print axioms outerFrameBox_side

end BoxCertifiedTubeTestData

end
end FamilyStickyBoxCertifiedTubeTestDataV1
