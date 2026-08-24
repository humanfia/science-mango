import Submission.Kakeya.Uniformity.TubeFamily

set_option autoImplicit false

namespace FamilyStickyCinematicL32WZL3UniformTubeSourceV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# The formal boundary of the Wang--Zahl `L_3` line chart

In Guth--Wang--Zahl, Section 2.1 (``Lines, tubes and shadings''),
`\mathcal L_3` consists of lines whose chosen unit direction has final
coordinate at least `1/2`.  The foundational project type
`UniformTubeFamily` stores only the resulting `Tube`; it has no line-space
object and therefore cannot reconstruct that source condition.

This structure records exactly the data that survives the conversion from a
finite `\mathcal L_3` source to a uniform tube family.  The absolute value is
the orientation-invariant image of the paper's oriented inequality.  It is a
source certificate, not a chart chosen separately after projection.
-/

/-- A finite source inside the fixed Wang--Zahl `L_3` chart, together with
its literal underlying uniform tube family. -/
structure WZL3UniformTubeSource
    (radius : NNReal) (iota : Type*) [DecidableEq iota] where
  family : UniformTubeFamily radius iota
  source : Finset iota
  source_direction_final_half : ∀ i, i ∈ source →
    (1 / 2 : Real) ≤ |(family.tubes i).axis.direction 2|

namespace WZL3UniformTubeSource

/-- Every subfamily of the original finite `L_3` source retains the fixed
vertical chart inequality. -/
theorem direction_final_half_of_mem_of_subset
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source) :
    ∀ i, i ∈ ambient →
      (1 / 2 : Real) ≤ |(S.family.tubes i).axis.direction 2| := by
  intro i hi
  exact S.source_direction_final_half i (hambient hi)

end WZL3UniformTubeSource

end
end FamilyStickyCinematicL32WZL3UniformTubeSourceV1
