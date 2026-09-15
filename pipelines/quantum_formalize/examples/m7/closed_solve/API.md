# Minimal closed recipe interface

`M7.ClosedSolve.closed_pointwise` consumes actual support-card equalities, both zero anchors and `M7.Connectivity.connected`. Its result is `M6.Final.PointwiseCorrect` at the two literal `M7.Supports.polynomial` inputs. It does not consume `AnswerCorrect` or an external distance function.

For a result `h`, the existing contract projections are:

| Projection | Existing sealed contract |
|---|---|
| `h.1` | CountingCorrect |
| `h.2.1` | ParametersCorrect |
| `h.2.2.1` | AnswerCorrect |
| `h.2.2.2.1` | ExecutionCorrect |
| `h.2.2.2.2` | StorageCorrect |

AnswerCorrect already provides actual solve=none iff signature degree zero, actual quantumDistance=none iff signature degree zero, and each actual solve result's minimal X/JZ witnesses with the `2*N` call bound. Transport.distance is definitionally the same quantumDistance on the literal polynomials. Existing `M7.Transport.actual_witness` carries such a solved witness through the actual recipe action; it already discharges M6 correctness internally using the accepted theorem.

This file describes interfaces, not an independent acceptance receipt. See PREFLIGHT.json and experiment/result.json for actual gates once present.
