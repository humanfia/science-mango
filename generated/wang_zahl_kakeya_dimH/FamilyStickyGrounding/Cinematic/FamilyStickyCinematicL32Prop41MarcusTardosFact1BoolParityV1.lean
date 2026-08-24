import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1

/-!
# Marcus--Tardos Fact 1: finite `K_{2,3}` parity kernel

An edge of the canonical `K_{2,3}` is indexed by its host and neighbor.
`crossingParity e f = true` means that the two literal drawn edges cross an
odd number of times away from their endpoints.  For two neighbors, the
self-crossing parity of their four-edge cycle is the xor of the two pairs of
opposite edges.

The field `rotation_crossing_parity` below is the one honest planar source
obligation: it is the mod-two intersection formula relating the rotations at
the two hosts to the three four-cycles.  It is not a no-triple,
intersection-reversal, or desired-existence premise.  The actual arc/Jordan
lane must prove this equality.  Everything after that equality is finite Bool
algebra and is proved here.

This is the precise finite part of Marcus--Tardos (2006), Fact 1 (p. 2):
equal host rotations force one `C4` to contain a pair of edges whose crossing
number is odd.
-/

abbrev K23Edge := Fin 2 × Fin 3

/-- Mod-two crossing number of the two opposite-edge pairs in the `C4`
through neighbors `j,k`. -/
def c4CrossingParity
    (crossingParity : K23Edge -> K23Edge -> Bool)
    (j k : Fin 3) : Bool :=
  Bool.xor
    (crossingParity (0, j) (1, k))
    (crossingParity (0, k) (1, j))

/-- Xor of the three canonical `C4` crossing parities. -/
def totalK23C4Parity
    (crossingParity : K23Edge -> K23Edge -> Bool) : Bool :=
  Bool.xor
    (c4CrossingParity crossingParity 0 1)
    (Bool.xor
      (c4CrossingParity crossingParity 1 2)
      (c4CrossingParity crossingParity 2 0))

/-- Finite parity data exported by an actual planar drawing.  Symmetry and
the zero diagonal record that this really is an unordered pair-crossing
matrix.  The last field is the sole topological producer obligation. -/
structure K23RotationCrossingParity where
  crossingParity : K23Edge -> K23Edge -> Bool
  crossing_symmetric : forall e f,
    crossingParity e f = crossingParity f e
  crossing_self : forall e, crossingParity e e = false
  hostRotationSign : Fin 2 -> Bool
  rotation_crossing_parity :
    totalK23C4Parity crossingParity =
      Bool.not (Bool.xor (hostRotationSign 0) (hostRotationSign 1))

def SameHostRotation (P : K23RotationCrossingParity) : Prop :=
  P.hostRotationSign 0 = P.hostRotationSign 1

theorem totalK23C4Parity_eq_true_of_sameHostRotation
    (P : K23RotationCrossingParity) (hsame : SameHostRotation P) :
    totalK23C4Parity P.crossingParity = true := by
  rw [P.rotation_crossing_parity]
  unfold SameHostRotation at hsame
  generalize hzero : P.hostRotationSign 0 = s
  generalize hone : P.hostRotationSign 1 = t
  cases s <;> cases t <;> simp_all

theorem one_canonical_c4_odd_of_total_eq_true
    (crossingParity : K23Edge -> K23Edge -> Bool)
    (htotal : totalK23C4Parity crossingParity = true) :
    c4CrossingParity crossingParity 0 1 = true ∨
      c4CrossingParity crossingParity 1 2 = true ∨
      c4CrossingParity crossingParity 2 0 = true := by
  generalize h01 : c4CrossingParity crossingParity 0 1 = p
  generalize h12 : c4CrossingParity crossingParity 1 2 = q
  generalize h20 : c4CrossingParity crossingParity 2 0 = r
  cases p <;> cases q <;> cases r <;> simp_all [totalK23C4Parity]

/-- Exact finite Fact 1 conclusion: two distinct neighbors determine a
four-edge cycle whose two opposite-edge crossing parities have odd xor. -/
theorem exists_c4_odd_of_sameHostRotation
    (P : K23RotationCrossingParity) (hsame : SameHostRotation P) :
    exists j k : Fin 3, j ≠ k ∧
      c4CrossingParity P.crossingParity j k = true := by
  have htotal := totalK23C4Parity_eq_true_of_sameHostRotation P hsame
  rcases one_canonical_c4_odd_of_total_eq_true P.crossingParity htotal with
      h01 | h12 | h20
  · exact ⟨0, 1, by decide, h01⟩
  · exact ⟨1, 2, by decide, h12⟩
  · exact ⟨2, 0, by decide, h20⟩

theorem exists_opposite_edge_pair_crossing_odd_of_sameHostRotation
    (P : K23RotationCrossingParity) (hsame : SameHostRotation P) :
    exists j k : Fin 3, j ≠ k ∧
      ((P.crossingParity (0, j) (1, k) = true ∧
          P.crossingParity (0, k) (1, j) = false) ∨
        (P.crossingParity (0, j) (1, k) = false ∧
          P.crossingParity (0, k) (1, j) = true)) := by
  rcases exists_c4_odd_of_sameHostRotation P hsame with ⟨j, k, hjk, hodd⟩
  refine ⟨j, k, hjk, ?_⟩
  unfold c4CrossingParity at hodd
  generalize hfirst : P.crossingParity (0, j) (1, k) = p at hodd
  generalize hsecond : P.crossingParity (0, k) (1, j) = q at hodd
  cases p <;> cases q <;> simp_all

/-- Corollary in the form used by Marcus--Tardos Corollary 7: if every
opposite-edge pair in every `C4` has even total parity, the host rotations
cannot be equal. -/
theorem hostRotations_ne_of_every_c4_even
    (P : K23RotationCrossingParity)
    (heven : forall j k : Fin 3, j ≠ k ->
      c4CrossingParity P.crossingParity j k = false) :
    ¬ SameHostRotation P := by
  intro hsame
  rcases exists_c4_odd_of_sameHostRotation P hsame with ⟨j, k, hjk, hodd⟩
  rw [heven j k hjk] at hodd
  contradiction

#print axioms totalK23C4Parity_eq_true_of_sameHostRotation
#print axioms one_canonical_c4_odd_of_total_eq_true
#print axioms exists_c4_odd_of_sameHostRotation
#print axioms exists_opposite_edge_pair_crossing_odd_of_sameHostRotation
#print axioms hostRotations_ne_of_every_c4_even

end FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
