import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubeC2GraphRectangleV1RepoV2

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1

noncomputable section

/-!
# Reusing the canonical cinematic derivative formulas for actual tube graphs
-/

def actualTubeGraphFirst {radius : NNReal} (T : Tube radius)
    (f f1 : Real → Real) : Real → Real :=
  cinematicTraceFirstValue f f1
    (skirtTubeGraphB T) (skirtTubeGraphC T) (skirtTubeGraphD T)

def actualTubeGraphSecond {radius : NNReal} (T : Tube radius)
    (f1 f2 : Real → Real) : Real → Real :=
  cinematicTraceSecondValue f1 f2
    (skirtTubeGraphB T) (skirtTubeGraphD T)

theorem hasDerivAt_actualTubeGraph
    {radius : NNReal} (T : Tube radius) {f f1 : Real → Real}
    {theta : Real} (hf : HasDerivAt f (f1 theta) theta) :
    HasDerivAt (actualTubeGraph T f)
      (actualTubeGraphFirst T f f1 theta) theta := by
  change HasDerivAt
    (cinematicTraceValue f (skirtTubeGraphA T) (skirtTubeGraphB T)
      (skirtTubeGraphC T) (skirtTubeGraphD T))
    (cinematicTraceFirstValue f f1 (skirtTubeGraphB T)
      (skirtTubeGraphC T) (skirtTubeGraphD T) theta) theta
  exact hasDerivAt_cinematicTraceValue f f1
    (skirtTubeGraphA T) (skirtTubeGraphB T)
    (skirtTubeGraphC T) (skirtTubeGraphD T) theta hf

theorem hasDerivAt_actualTubeGraphFirst
    {radius : NNReal} (T : Tube radius) {f f1 f2 : Real → Real}
    {theta : Real} (hf : HasDerivAt f (f1 theta) theta)
    (hf1 : HasDerivAt f1 (f2 theta) theta) :
    HasDerivAt (actualTubeGraphFirst T f f1)
      (actualTubeGraphSecond T f1 f2 theta) theta := by
  exact hasDerivAt_cinematicTraceFirstValue f f1 f2
    (skirtTubeGraphB T) (skirtTubeGraphC T) (skirtTubeGraphD T)
    theta hf hf1

theorem continuousAt_actualTubeGraphFirst
    {radius : NNReal} (T : Tube radius) {f f1 f2 : Real → Real}
    {theta : Real} (hf : HasDerivAt f (f1 theta) theta)
    (hf1 : HasDerivAt f1 (f2 theta) theta) :
    ContinuousAt (actualTubeGraphFirst T f f1) theta :=
  (hasDerivAt_actualTubeGraphFirst T hf hf1).continuousAt

#print axioms actualTubeGraphFirst
#print axioms actualTubeGraphSecond
#print axioms hasDerivAt_actualTubeGraph
#print axioms hasDerivAt_actualTubeGraphFirst
#print axioms continuousAt_actualTubeGraphFirst

end

end FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
