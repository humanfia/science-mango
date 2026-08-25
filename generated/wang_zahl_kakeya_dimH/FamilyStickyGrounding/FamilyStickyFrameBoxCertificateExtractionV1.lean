import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap
import FamilyStickyGrounding.FamilyStickyActualDenseLatticePointBalanceV1

open Set
open scoped NNReal

namespace FamilyStickyFrameBoxCertificateExtractionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyDenseLatticeMultiBoxPointCountV1

noncomputable section

/-!
# Extracting actual outer frame boxes for the translation grid

`HasBoxDimensions` already contains the needed outer `FrameBox`; the existing
`BoxDimensionsCertificate` API exposes it as data.  This module makes one
choice for every finite test body, proves the literal carrier containment,
and uses those boxes to construct the dense lattice and its actual
realization.  Thus the point-count adapter no longer receives the
test-body-to-box containment as an independent callback.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]
  (G : ActualTubeTranslationGrid delta translation tubeIndex)
  {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}

/-- The existing data-bearing certificate, chosen once for each test body. -/
noncomputable def testBoxCertificate
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) :
    BoxDimensionsCertificate C (side K) (G.testBody K) :=
  Classical.choice ((hdim K).nonempty_boxDimensionsCertificate)

/-- The actual outer oriented box extracted from `HasBoxDimensions`. -/
noncomputable def testOuterBox
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) : FrameBox :=
  (testBoxCertificate G hdim K).box

theorem testOuterBox_side
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) :
    (testOuterBox G hdim K).side = side K :=
  (testBoxCertificate G hdim K).side_eq

theorem testBody_subset_testOuterBox
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) :
    (G.testBody K : Set Space) ⊆ (testOuterBox G hdim K).carrier := by
  intro x hx
  change x ∈ (testBoxCertificate G hdim K).box.body
  exact (testBoxCertificate G hdim K).outer_le hx

theorem rescaled_testOuterBox_subset_testBody
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) :
    ((testOuterBox G hdim K).rescale C⁻¹).carrier ⊆
      (G.testBody K : Set Space) := by
  intro x hx
  exact (testBoxCertificate G hdim K).inner_le hx

/-- Dense lattice whose oriented boxes are extracted from the actual test
bodies.  Only spacing and site counts remain as numerical inputs. -/
noncomputable def denseLatticeOfBoxDimensions
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (spacing : Fin G.testCard -> Fin 3 -> NNReal)
    (siteCount : Fin G.testCard -> Fin 3 -> Nat)
    (hspacing : forall K i, 0 < spacing K i) :
    DenseMultiBoxLattice (Fin G.testCard) where
  box := testOuterBox G hdim
  spacing := spacing
  siteCount := siteCount
  spacing_pos := hspacing

theorem denseLatticeOfBoxDimensions_box_side
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (spacing : Fin G.testCard -> Fin 3 -> NNReal)
    (siteCount : Fin G.testCard -> Fin 3 -> Nat)
    (hspacing : forall K i, 0 < spacing K i)
    (K : Fin G.testCard) :
    ((denseLatticeOfBoxDimensions G hdim spacing siteCount hspacing).box K).side =
      side K :=
  testOuterBox_side G hdim K

/-- Constructor for the actual dense realization.  The box-containment field
is discharged from `HasBoxDimensions`; only the literal equivalence with the
finite product grid and its vector identity are supplied. -/
noncomputable def denseRealizationOfBoxDimensions
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (spacing : Fin G.testCard -> Fin 3 -> NNReal)
    (siteCount : Fin G.testCard -> Fin 3 -> Nat)
    (hspacing : forall K i, 0 < spacing K i)
    (decode : translation ≃
      (denseLatticeOfBoxDimensions G hdim spacing siteCount hspacing).Choice)
    (hgrid : forall g,
      G.gridVector g =
        (denseLatticeOfBoxDimensions G hdim spacing siteCount hspacing).choiceVector
          (decode g)) :
    FamilyStickyActualDenseLatticePointBalanceV1.ActualTubeTranslationGrid.IsDenseMultiBoxLatticeRealization
      G (denseLatticeOfBoxDimensions G hdim spacing siteCount hspacing) where
  decode := decode
  gridVector_eq := hgrid
  testBody_subset_box := testBody_subset_testOuterBox G hdim

#print axioms testOuterBox_side
#print axioms testBody_subset_testOuterBox
#print axioms rescaled_testOuterBox_subset_testBody
#print axioms denseLatticeOfBoxDimensions_box_side
#print axioms denseRealizationOfBoxDimensions

end ActualTubeTranslationGrid

end

end FamilyStickyFrameBoxCertificateExtractionV1
