import ArchonPhysics.ActualSixSiteNearResonantModularCertificate
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

/-!
# Polynomial inverse certificate for the six-site modular residual

The explicit residual and inverse coefficient cubes satisfy one polynomial
Bezout identity modulo the three companion quintics. The quotient
polynomials were generated externally, but the displayed identity is checked
again by Lean's kernel via ring; no native evaluator is part of the proof.
-/

open scoped BigOperators

namespace ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate

noncomputable section

abbrev SpectralVariable := Fin 3

def monomial (i j k : Nat) (coefficient : ZMod 103) :
    MvPolynomial SpectralVariable (ZMod 103) :=
  MvPolynomial.C coefficient * MvPolynomial.X 0 ^ i *
    MvPolynomial.X 1 ^ j * MvPolynomial.X 2 ^ k

def residualPolynomial103 : MvPolynomial SpectralVariable (ZMod 103) :=
  ∑ a : CubeIndex,
    monomial a.1.val a.2.1.val a.2.2.val (residualCube103 a)

def inversePolynomial103 : MvPolynomial SpectralVariable (ZMod 103) :=
  ∑ a : CubeIndex,
    monomial a.1.val a.2.1.val a.2.2.val (inverseCube103 a)

def quotientQuintic103 (r : SpectralVariable) :
    MvPolynomial SpectralVariable (ZMod 103) :=
  MvPolynomial.X r ^ 5 +
    MvPolynomial.C 92 * MvPolynomial.X r ^ 4 +
    MvPolynomial.C 20 * MvPolynomial.X r ^ 3 +
    MvPolynomial.C 14 * MvPolynomial.X r ^ 2 +
    MvPolynomial.C 80 * MvPolynomial.X r +
    MvPolynomial.C 76

def quotientX103 : MvPolynomial SpectralVariable (ZMod 103) :=
  monomial 3 8 8 (-16) +
  monomial 3 8 7 (-17) +
  monomial 3 8 6 (-50) +
  monomial 3 8 5 44 +
  monomial 3 8 4 33 +
  monomial 3 8 3 45 +
  monomial 3 8 2 29 +
  monomial 3 8 1 43 +
  monomial 3 8 0 (-10) +
  monomial 3 7 8 (-17) +
  monomial 3 7 7 29 +
  monomial 3 7 6 (-2) +
  monomial 3 7 5 (-42) +
  monomial 3 7 4 18 +
  monomial 3 7 3 (-17) +
  monomial 3 7 2 (-5) +
  monomial 3 7 1 19 +
  monomial 3 7 0 7 +
  monomial 3 6 8 (-50) +
  monomial 3 6 7 (-2) +
  monomial 3 6 6 (-30) +
  monomial 3 6 5 (-7) +
  monomial 3 6 4 (-31) +
  monomial 3 6 3 (-28) +
  monomial 3 6 2 (-2) +
  monomial 3 6 1 18 +
  monomial 3 6 0 (-37) +
  monomial 3 5 8 44 +
  monomial 3 5 7 (-42) +
  monomial 3 5 6 (-7) +
  monomial 3 5 4 49 +
  monomial 3 5 3 (-45) +
  monomial 3 5 2 23 +
  monomial 3 5 1 6 +
  monomial 3 5 0 (-20) +
  monomial 3 4 8 33 +
  monomial 3 4 7 18 +
  monomial 3 4 6 (-31) +
  monomial 3 4 5 49 +
  monomial 3 4 4 13 +
  monomial 3 4 3 15 +
  monomial 3 4 2 (-41) +
  monomial 3 4 1 4 +
  monomial 3 4 0 21 +
  monomial 3 3 8 45 +
  monomial 3 3 7 (-17) +
  monomial 3 3 6 (-28) +
  monomial 3 3 5 (-45) +
  monomial 3 3 4 15 +
  monomial 3 3 3 (-24) +
  monomial 3 3 2 45 +
  monomial 3 3 1 (-17) +
  monomial 3 3 0 (-33) +
  monomial 3 2 8 29 +
  monomial 3 2 7 (-5) +
  monomial 3 2 6 (-2) +
  monomial 3 2 5 23 +
  monomial 3 2 4 (-41) +
  monomial 3 2 3 45 +
  monomial 3 2 2 27 +
  monomial 3 2 1 (-7) +
  monomial 3 2 0 19 +
  monomial 3 1 8 43 +
  monomial 3 1 7 19 +
  monomial 3 1 6 18 +
  monomial 3 1 5 6 +
  monomial 3 1 4 4 +
  monomial 3 1 3 (-17) +
  monomial 3 1 2 (-7) +
  monomial 3 1 1 5 +
  monomial 3 1 0 (-38) +
  monomial 3 0 8 (-10) +
  monomial 3 0 7 7 +
  monomial 3 0 6 (-37) +
  monomial 3 0 5 (-20) +
  monomial 3 0 4 21 +
  monomial 3 0 3 (-33) +
  monomial 3 0 2 19 +
  monomial 3 0 1 (-38) +
  monomial 3 0 0 2 +
  monomial 2 8 8 13 +
  monomial 2 8 7 48 +
  monomial 2 8 6 (-37) +
  monomial 2 8 5 30 +
  monomial 2 8 4 (-31) +
  monomial 2 8 3 (-37) +
  monomial 2 8 2 5 +
  monomial 2 8 1 (-23) +
  monomial 2 7 8 48 +
  monomial 2 7 7 (-15) +
  monomial 2 7 6 (-48) +
  monomial 2 7 5 (-1) +
  monomial 2 7 4 (-1) +
  monomial 2 7 3 (-39) +
  monomial 2 7 2 (-40) +
  monomial 2 7 1 6 +
  monomial 2 7 0 (-11) +
  monomial 2 6 8 (-37) +
  monomial 2 6 7 (-48) +
  monomial 2 6 6 (-8) +
  monomial 2 6 5 33 +
  monomial 2 6 4 47 +
  monomial 2 6 3 (-7) +
  monomial 2 6 2 (-13) +
  monomial 2 6 1 (-13) +
  monomial 2 6 0 47 +
  monomial 2 5 8 30 +
  monomial 2 5 7 (-1) +
  monomial 2 5 6 33 +
  monomial 2 5 5 (-2) +
  monomial 2 5 4 (-49) +
  monomial 2 5 3 5 +
  monomial 2 5 2 (-5) +
  monomial 2 5 1 24 +
  monomial 2 5 0 14 +
  monomial 2 4 8 (-31) +
  monomial 2 4 7 (-1) +
  monomial 2 4 6 47 +
  monomial 2 4 5 (-49) +
  monomial 2 4 4 7 +
  monomial 2 4 3 41 +
  monomial 2 4 2 20 +
  monomial 2 4 1 22 +
  monomial 2 4 0 36 +
  monomial 2 3 8 (-37) +
  monomial 2 3 7 (-39) +
  monomial 2 3 6 (-7) +
  monomial 2 3 5 5 +
  monomial 2 3 4 41 +
  monomial 2 3 3 (-16) +
  monomial 2 3 2 (-36) +
  monomial 2 3 1 16 +
  monomial 2 3 0 (-7) +
  monomial 2 2 8 5 +
  monomial 2 2 7 (-40) +
  monomial 2 2 6 (-13) +
  monomial 2 2 5 (-5) +
  monomial 2 2 4 20 +
  monomial 2 2 3 (-36) +
  monomial 2 2 2 18 +
  monomial 2 2 1 (-45) +
  monomial 2 2 0 (-9) +
  monomial 2 1 8 (-23) +
  monomial 2 1 7 6 +
  monomial 2 1 6 (-13) +
  monomial 2 1 5 24 +
  monomial 2 1 4 22 +
  monomial 2 1 3 16 +
  monomial 2 1 2 (-45) +
  monomial 2 1 1 15 +
  monomial 2 1 0 28 +
  monomial 2 0 7 (-11) +
  monomial 2 0 6 47 +
  monomial 2 0 5 14 +
  monomial 2 0 4 36 +
  monomial 2 0 3 (-7) +
  monomial 2 0 2 (-9) +
  monomial 2 0 1 28 +
  monomial 2 0 0 30 +
  monomial 1 8 8 1 +
  monomial 1 8 7 42 +
  monomial 1 8 6 48 +
  monomial 1 8 5 (-42) +
  monomial 1 8 4 (-2) +
  monomial 1 8 3 4 +
  monomial 1 8 2 (-12) +
  monomial 1 8 1 38 +
  monomial 1 8 0 (-43) +
  monomial 1 7 8 42 +
  monomial 1 7 7 (-50) +
  monomial 1 7 6 40 +
  monomial 1 7 5 12 +
  monomial 1 7 4 17 +
  monomial 1 7 3 6 +
  monomial 1 7 2 (-22) +
  monomial 1 7 1 (-10) +
  monomial 1 7 0 (-13) +
  monomial 1 6 8 48 +
  monomial 1 6 7 40 +
  monomial 1 6 6 (-20) +
  monomial 1 6 5 (-5) +
  monomial 1 6 4 19 +
  monomial 1 6 3 7 +
  monomial 1 6 2 39 +
  monomial 1 6 1 (-6) +
  monomial 1 6 0 (-6) +
  monomial 1 5 8 (-42) +
  monomial 1 5 7 12 +
  monomial 1 5 6 (-5) +
  monomial 1 5 5 (-47) +
  monomial 1 5 4 26 +
  monomial 1 5 3 14 +
  monomial 1 5 2 28 +
  monomial 1 5 1 (-48) +
  monomial 1 5 0 (-6) +
  monomial 1 4 8 (-2) +
  monomial 1 4 7 17 +
  monomial 1 4 6 19 +
  monomial 1 4 5 26 +
  monomial 1 4 4 (-29) +
  monomial 1 4 3 30 +
  monomial 1 4 2 8 +
  monomial 1 4 1 2 +
  monomial 1 4 0 (-20) +
  monomial 1 3 8 4 +
  monomial 1 3 7 6 +
  monomial 1 3 6 7 +
  monomial 1 3 5 14 +
  monomial 1 3 4 30 +
  monomial 1 3 3 40 +
  monomial 1 3 2 (-44) +
  monomial 1 3 1 45 +
  monomial 1 3 0 (-36) +
  monomial 1 2 8 (-12) +
  monomial 1 2 7 (-22) +
  monomial 1 2 6 39 +
  monomial 1 2 5 28 +
  monomial 1 2 4 8 +
  monomial 1 2 3 (-44) +
  monomial 1 2 2 (-8) +
  monomial 1 2 1 (-23) +
  monomial 1 2 0 37 +
  monomial 1 1 8 38 +
  monomial 1 1 7 (-10) +
  monomial 1 1 6 (-6) +
  monomial 1 1 5 (-48) +
  monomial 1 1 4 2 +
  monomial 1 1 3 45 +
  monomial 1 1 2 (-23) +
  monomial 1 1 1 24 +
  monomial 1 1 0 6 +
  monomial 1 0 8 (-43) +
  monomial 1 0 7 (-13) +
  monomial 1 0 6 (-6) +
  monomial 1 0 5 (-6) +
  monomial 1 0 4 (-20) +
  monomial 1 0 3 (-36) +
  monomial 1 0 2 37 +
  monomial 1 0 1 6 +
  monomial 1 0 0 9 +
  monomial 0 8 8 19 +
  monomial 0 8 7 7 +
  monomial 0 8 6 4 +
  monomial 0 8 5 (-30) +
  monomial 0 8 4 (-21) +
  monomial 0 8 3 6 +
  monomial 0 8 2 3 +
  monomial 0 8 1 (-27) +
  monomial 0 8 0 (-44) +
  monomial 0 7 8 7 +
  monomial 0 7 7 11 +
  monomial 0 7 6 (-7) +
  monomial 0 7 5 17 +
  monomial 0 7 4 (-15) +
  monomial 0 7 3 39 +
  monomial 0 7 2 (-42) +
  monomial 0 7 1 (-23) +
  monomial 0 7 0 7 +
  monomial 0 6 8 4 +
  monomial 0 6 7 (-7) +
  monomial 0 6 6 (-45) +
  monomial 0 6 5 (-24) +
  monomial 0 6 4 12 +
  monomial 0 6 3 (-23) +
  monomial 0 6 2 24 +
  monomial 0 6 1 (-44) +
  monomial 0 6 0 (-18) +
  monomial 0 5 8 (-30) +
  monomial 0 5 7 17 +
  monomial 0 5 6 (-24) +
  monomial 0 5 5 (-32) +
  monomial 0 5 4 2 +
  monomial 0 5 3 19 +
  monomial 0 5 2 (-23) +
  monomial 0 5 1 (-32) +
  monomial 0 5 0 42 +
  monomial 0 4 8 (-21) +
  monomial 0 4 7 (-15) +
  monomial 0 4 6 12 +
  monomial 0 4 5 2 +
  monomial 0 4 4 16 +
  monomial 0 4 3 50 +
  monomial 0 4 2 (-19) +
  monomial 0 4 1 (-11) +
  monomial 0 4 0 (-49) +
  monomial 0 3 8 6 +
  monomial 0 3 7 39 +
  monomial 0 3 6 (-23) +
  monomial 0 3 5 19 +
  monomial 0 3 4 50 +
  monomial 0 3 3 (-43) +
  monomial 0 3 2 (-1) +
  monomial 0 3 1 32 +
  monomial 0 3 0 (-5) +
  monomial 0 2 8 3 +
  monomial 0 2 7 (-42) +
  monomial 0 2 6 24 +
  monomial 0 2 5 (-23) +
  monomial 0 2 4 (-19) +
  monomial 0 2 3 (-1) +
  monomial 0 2 2 (-13) +
  monomial 0 2 1 42 +
  monomial 0 2 0 (-6) +
  monomial 0 1 8 (-27) +
  monomial 0 1 7 (-23) +
  monomial 0 1 6 (-44) +
  monomial 0 1 5 (-32) +
  monomial 0 1 4 (-11) +
  monomial 0 1 3 32 +
  monomial 0 1 2 42 +
  monomial 0 1 1 (-2) +
  monomial 0 1 0 42 +
  monomial 0 0 8 (-44) +
  monomial 0 0 7 7 +
  monomial 0 0 6 (-18) +
  monomial 0 0 5 42 +
  monomial 0 0 4 (-49) +
  monomial 0 0 3 (-5) +
  monomial 0 0 2 (-6) +
  monomial 0 0 1 42 +
  monomial 0 0 0 33


def quotientY103 : MvPolynomial SpectralVariable (ZMod 103) :=
  monomial 4 3 8 (-19) +
  monomial 4 3 7 46 +
  monomial 4 3 6 (-34) +
  monomial 4 3 5 18 +
  monomial 4 3 4 (-15) +
  monomial 4 3 3 9 +
  monomial 4 3 2 5 +
  monomial 4 3 1 (-51) +
  monomial 4 3 0 (-39) +
  monomial 4 2 8 43 +
  monomial 4 2 7 39 +
  monomial 4 2 6 (-31) +
  monomial 4 2 5 47 +
  monomial 4 2 4 34 +
  monomial 4 2 3 27 +
  monomial 4 2 2 22 +
  monomial 4 2 1 26 +
  monomial 4 2 0 28 +
  monomial 4 1 8 (-5) +
  monomial 4 1 7 (-45) +
  monomial 4 1 6 (-10) +
  monomial 4 1 5 (-12) +
  monomial 4 1 4 33 +
  monomial 4 1 3 (-16) +
  monomial 4 1 2 (-34) +
  monomial 4 1 1 39 +
  monomial 4 1 0 20 +
  monomial 4 0 8 (-13) +
  monomial 4 0 7 (-10) +
  monomial 4 0 6 (-7) +
  monomial 4 0 5 (-50) +
  monomial 4 0 4 11 +
  monomial 4 0 3 (-32) +
  monomial 4 0 2 (-40) +
  monomial 4 0 1 (-49) +
  monomial 4 0 0 (-22) +
  monomial 3 3 8 33 +
  monomial 3 3 7 3 +
  monomial 3 3 6 6 +
  monomial 3 3 5 34 +
  monomial 3 3 4 23 +
  monomial 3 3 3 (-42) +
  monomial 3 3 2 21 +
  monomial 3 3 1 5 +
  monomial 3 3 0 46 +
  monomial 3 2 8 (-46) +
  monomial 3 2 7 (-34) +
  monomial 3 2 6 25 +
  monomial 3 2 5 33 +
  monomial 3 2 4 36 +
  monomial 3 2 3 38 +
  monomial 3 2 2 (-1) +
  monomial 3 2 1 (-36) +
  monomial 3 2 0 16 +
  monomial 3 1 8 (-27) +
  monomial 3 1 7 40 +
  monomial 3 1 6 (-32) +
  monomial 3 1 5 (-35) +
  monomial 3 1 4 (-35) +
  monomial 3 1 3 27 +
  monomial 3 1 2 (-43) +
  monomial 3 1 1 (-22) +
  monomial 3 1 0 (-13) +
  monomial 3 0 8 (-11) +
  monomial 3 0 7 16 +
  monomial 3 0 6 (-36) +
  monomial 3 0 5 (-7) +
  monomial 3 0 4 42 +
  monomial 3 0 3 (-12) +
  monomial 3 0 2 14 +
  monomial 3 0 1 (-7) +
  monomial 3 0 0 (-26) +
  monomial 2 3 8 34 +
  monomial 2 3 7 (-4) +
  monomial 2 3 6 47 +
  monomial 2 3 5 (-22) +
  monomial 2 3 4 (-12) +
  monomial 2 3 3 (-19) +
  monomial 2 3 2 50 +
  monomial 2 3 1 6 +
  monomial 2 3 0 (-45) +
  monomial 2 2 8 (-42) +
  monomial 2 2 7 13 +
  monomial 2 2 6 42 +
  monomial 2 2 5 26 +
  monomial 2 2 4 (-14) +
  monomial 2 2 3 (-38) +
  monomial 2 2 2 (-6) +
  monomial 2 2 1 43 +
  monomial 2 2 0 35 +
  monomial 2 1 8 38 +
  monomial 2 1 7 (-46) +
  monomial 2 1 6 30 +
  monomial 2 1 5 12 +
  monomial 2 1 4 (-26) +
  monomial 2 1 3 (-37) +
  monomial 2 1 2 (-7) +
  monomial 2 1 1 (-12) +
  monomial 2 1 0 (-9) +
  monomial 2 0 8 39 +
  monomial 2 0 7 (-30) +
  monomial 2 0 6 (-28) +
  monomial 2 0 5 51 +
  monomial 2 0 4 (-48) +
  monomial 2 0 3 (-33) +
  monomial 2 0 2 (-43) +
  monomial 2 0 1 (-36) +
  monomial 2 0 0 (-20) +
  monomial 1 3 8 (-8) +
  monomial 1 3 7 (-25) +
  monomial 1 3 6 (-36) +
  monomial 1 3 5 36 +
  monomial 1 3 4 (-18) +
  monomial 1 3 3 23 +
  monomial 1 3 2 47 +
  monomial 1 3 1 (-2) +
  monomial 1 3 0 (-48) +
  monomial 1 2 8 (-10) +
  monomial 1 2 7 (-30) +
  monomial 1 2 6 3 +
  monomial 1 2 5 39 +
  monomial 1 2 4 (-3) +
  monomial 1 2 3 (-30) +
  monomial 1 2 2 19 +
  monomial 1 2 1 (-37) +
  monomial 1 2 0 37 +
  monomial 1 1 8 14 +
  monomial 1 1 7 (-49) +
  monomial 1 1 6 (-16) +
  monomial 1 1 5 (-37) +
  monomial 1 1 4 29 +
  monomial 1 1 3 47 +
  monomial 1 1 2 (-30) +
  monomial 1 1 1 (-37) +
  monomial 1 1 0 38 +
  monomial 1 0 8 (-13) +
  monomial 1 0 7 (-49) +
  monomial 1 0 6 7 +
  monomial 1 0 5 42 +
  monomial 1 0 4 (-12) +
  monomial 1 0 3 (-7) +
  monomial 1 0 2 10 +
  monomial 1 0 1 (-22) +
  monomial 1 0 0 25 +
  monomial 0 3 8 (-12) +
  monomial 0 3 7 (-10) +
  monomial 0 3 6 (-32) +
  monomial 0 3 5 (-6) +
  monomial 0 3 4 (-31) +
  monomial 0 3 3 26 +
  monomial 0 3 2 (-3) +
  monomial 0 3 1 (-46) +
  monomial 0 3 0 50 +
  monomial 0 2 8 (-39) +
  monomial 0 2 7 (-4) +
  monomial 0 2 6 16 +
  monomial 0 2 5 9 +
  monomial 0 2 4 (-14) +
  monomial 0 2 3 47 +
  monomial 0 2 2 (-46) +
  monomial 0 2 1 40 +
  monomial 0 2 0 26 +
  monomial 0 1 8 (-15) +
  monomial 0 1 7 9 +
  monomial 0 1 6 (-14) +
  monomial 0 1 5 41 +
  monomial 0 1 4 (-30) +
  monomial 0 1 3 (-7) +
  monomial 0 1 2 (-3) +
  monomial 0 1 1 37 +
  monomial 0 1 0 (-39) +
  monomial 0 0 8 (-47) +
  monomial 0 0 7 (-18) +
  monomial 0 0 6 2 +
  monomial 0 0 5 11 +
  monomial 0 0 4 (-25) +
  monomial 0 0 3 (-49) +
  monomial 0 0 2 (-19) +
  monomial 0 0 1 9 +
  monomial 0 0 0 47


def quotientZ103 : MvPolynomial SpectralVariable (ZMod 103) :=
  monomial 4 4 3 36 +
  monomial 4 4 2 43 +
  monomial 4 4 1 20 +
  monomial 4 4 0 (-35) +
  monomial 4 3 3 (-9) +
  monomial 4 3 2 17 +
  monomial 4 3 1 16 +
  monomial 4 3 0 5 +
  monomial 4 2 3 (-3) +
  monomial 4 2 2 (-11) +
  monomial 4 2 1 30 +
  monomial 4 2 0 39 +
  monomial 4 1 3 30 +
  monomial 4 1 2 (-13) +
  monomial 4 1 1 31 +
  monomial 4 1 0 (-8) +
  monomial 4 0 3 22 +
  monomial 4 0 2 17 +
  monomial 4 0 1 35 +
  monomial 4 0 0 13 +
  monomial 3 4 3 (-9) +
  monomial 3 4 2 17 +
  monomial 3 4 1 16 +
  monomial 3 4 0 5 +
  monomial 3 3 3 (-23) +
  monomial 3 3 2 5 +
  monomial 3 3 1 (-47) +
  monomial 3 3 0 21 +
  monomial 3 2 3 (-40) +
  monomial 3 2 2 33 +
  monomial 3 2 1 37 +
  monomial 3 2 0 16 +
  monomial 3 1 3 (-50) +
  monomial 3 1 2 (-17) +
  monomial 3 1 1 7 +
  monomial 3 1 0 8 +
  monomial 3 0 3 (-45) +
  monomial 3 0 2 (-38) +
  monomial 3 0 1 35 +
  monomial 3 0 0 (-11) +
  monomial 2 4 3 (-3) +
  monomial 2 4 2 (-11) +
  monomial 2 4 1 30 +
  monomial 2 4 0 39 +
  monomial 2 3 3 (-40) +
  monomial 2 3 2 33 +
  monomial 2 3 1 37 +
  monomial 2 3 0 16 +
  monomial 2 2 3 (-35) +
  monomial 2 2 2 8 +
  monomial 2 2 1 46 +
  monomial 2 2 0 (-37) +
  monomial 2 1 3 (-28) +
  monomial 2 1 2 3 +
  monomial 2 1 1 (-18) +
  monomial 2 1 0 (-7) +
  monomial 2 0 3 (-22) +
  monomial 2 0 2 (-7) +
  monomial 2 0 1 (-39) +
  monomial 1 4 3 30 +
  monomial 1 4 2 (-13) +
  monomial 1 4 1 31 +
  monomial 1 4 0 (-8) +
  monomial 1 3 3 (-50) +
  monomial 1 3 2 (-17) +
  monomial 1 3 1 7 +
  monomial 1 3 0 8 +
  monomial 1 2 3 (-28) +
  monomial 1 2 2 3 +
  monomial 1 2 1 (-18) +
  monomial 1 2 0 (-7) +
  monomial 1 1 3 (-26) +
  monomial 1 1 2 30 +
  monomial 1 1 1 (-18) +
  monomial 1 1 0 (-26) +
  monomial 1 0 3 13 +
  monomial 1 0 2 3 +
  monomial 1 0 1 (-28) +
  monomial 1 0 0 (-50) +
  monomial 0 4 3 22 +
  monomial 0 4 2 17 +
  monomial 0 4 1 35 +
  monomial 0 4 0 13 +
  monomial 0 3 3 (-45) +
  monomial 0 3 2 (-38) +
  monomial 0 3 1 35 +
  monomial 0 3 0 (-11) +
  monomial 0 2 3 (-22) +
  monomial 0 2 2 (-7) +
  monomial 0 2 1 (-39) +
  monomial 0 1 3 13 +
  monomial 0 1 2 3 +
  monomial 0 1 1 (-28) +
  monomial 0 1 0 (-50) +
  monomial 0 0 3 17 +
  monomial 0 0 2 1 +
  monomial 0 0 1 (-12) +
  monomial 0 0 0 (-45)


abbrev CorrectionIndex := Fin 9 × (Fin 9 × Fin 9)

def correctionCoefficientArray103 : Array Nat := #[
    4173, 5194, 9144, 10199, 14949, 9985, 10105, 5490, 4661, 5186, 6080, 14117,
    18617, 22075, 17888, 14194, 8628, 3093, 9120, 14043, 24644, 27225, 34468, 24443,
    18984, 8207, 5952, 10113, 18551, 27265, 31790, 34784, 28170, 18074, 10888, 4540,
    14815, 21973, 34390, 34680, 44188, 26535, 21956, 10176, 6177, 10007, 17869, 24456,
    28192, 26621, 19898, 11941, 7058, 2759, 10078, 14163, 19016, 17972, 21971, 11920,
    8761, 4212, 2442, 5447, 8673, 8192, 10811, 10201, 7069, 4235, 2444, 1192,
    4626, 3046, 5905, 4489, 6118, 2736, 2405, 1181, 548, 5174, 6092, 14101,
    18633, 22087, 17844, 14166, 8644, 3101, 5988, 12474, 24671, 29240, 37356, 30403,
    24831, 12917, 5330, 14027, 24739, 37326, 52213, 56722, 44378, 34617, 23984, 9101,
    18617, 29294, 52163, 63802, 79462, 57982, 50781, 30330, 14700, 22047, 37342, 56654,
    79384, 90142, 75005, 56061, 37707, 14045, 17817, 30435, 44381, 57999, 75075, 56111,
    40785, 25139, 11813, 14152, 24880, 34579, 50753, 56037, 40725, 27131, 19157, 8723,
    8662, 12822, 23850, 30207, 37673, 25053, 19157, 11606, 5189, 3092, 5330, 9102,
    14685, 14029, 11822, 8713, 5182, 2402, 9092, 14129, 24606, 27305, 34448, 24417,
    18996, 8217, 5918, 14101, 24703, 37386, 52195, 56772, 44362, 34675, 23932, 9029,
    24550, 37312, 54818, 68365, 79167, 64003, 52951, 30599, 15063, 27253, 52051, 68205,
    87565, 104022, 86140, 63379, 42277, 16676, 34408, 56656, 79061, 104040, 136707, 99306,
    78817, 46990, 25885, 24423, 44393, 64077, 86233, 99393, 79209, 59594, 40962, 16881,
    18942, 34633, 52998, 63505, 78845, 59616, 48383, 29837, 16520, 8215, 23844, 30493,
    42254, 46961, 40942, 29805, 19402, 9086, 5947, 9087, 15066, 16681, 25948, 16912,
    16489, 9116, 4272, 10157, 18581, 27201, 31848, 34716, 28196, 18066, 10896, 4524,
    18617, 29316, 52233, 63774, 79484, 58088, 50801, 30252, 14708, 27199, 52211, 68169,
    87477, 104062, 86164, 63455, 42291, 16690, 31724, 63784, 87547, 116204, 142295, 108989,
    77095, 52184, 24383, 34688, 79454, 104016, 142359, 167818, 130866, 91099, 62085, 29261,
    28211, 58079, 86230, 108964, 130921, 102697, 72525, 50925, 24455, 17974, 50756, 63463,
    77081, 91046, 72466, 49850, 34158, 16284, 10826, 30245, 42245, 52185, 62076, 50924,
    34123, 19830, 11876, 4515, 14679, 16633, 24366, 29265, 24426, 16249, 11905, 5684,
    14835, 21973, 34364, 34760, 44164, 26565, 21986, 10142, 6167, 21981, 37302, 56722,
    79472, 90084, 75167, 56101, 37679, 14011, 34314, 56584, 79083, 104020, 136625, 99304,
    78897, 47022, 25871, 34778, 79456, 103990, 142415, 167796, 130862, 91181, 62043, 29209,
    44278, 90222, 136707, 167786, 210952, 157063, 117144, 69200, 34385, 26548, 75116, 99373,
    130925, 157033, 139247, 88394, 58087, 28173, 21983, 56069, 78835, 91117, 117123, 88329,
    57136, 35253, 19366, 10189, 37710, 47007, 62083, 69269, 58044, 35327, 21370, 9025,
    6158, 13998, 25897, 29225, 34364, 28174, 19401, 9008, 7425, 10001, 17874, 24393,
    28250, 26597, 19917, 11911, 7089, 2754, 17874, 30309, 44397, 58022, 75112, 56069,
    40750, 25113, 11733, 24393, 44397, 64091, 86247, 99344, 79153, 59620, 40962, 16903,
    28250, 58022, 86247, 108937, 130865, 102655, 72516, 50932, 24468, 26597, 75112, 99344,
    130865, 157128, 139189, 88329, 58028, 28181, 19917, 56069, 79153, 102655, 139189, 106637,
    86363, 54019, 26155, 11911, 40750, 59620, 72516, 88329, 86363, 49122, 31370, 16487,
    7089, 25113, 40962, 50932, 58028, 54019, 31370, 17621, 9640, 2754, 11733, 16903,
    24468, 28181, 26155, 16487, 9640, 4289, 10070, 14140, 18996, 18015, 21925, 11901,
    8701, 4210, 2410, 14140, 24793, 34694, 50707, 56034, 40722, 27085, 19140, 8763,
    18996, 34694, 53005, 63488, 78871, 59652, 48414, 29879, 16490, 18015, 50707, 63488,
    77096, 91061, 72521, 49845, 34132, 16215, 21925, 56034, 78871, 91061, 117139, 88385,
    56997, 35287, 19391, 11901, 40722, 59652, 72521, 88385, 86366, 49070, 31405, 16481,
    8701, 27085, 48414, 49845, 56997, 49070, 34316, 15647, 11639, 4210, 19140, 29879,
    34132, 35287, 31405, 15647, 7914, 5807, 2410, 8763, 16490, 16215, 19391, 16481,
    11639, 5807, 2642, 5495, 8649, 8141, 10893, 10143, 7094, 4234, 2437, 1195,
    8649, 12790, 23850, 30277, 37654, 25102, 19133, 11538, 5180, 8141, 23850, 30461,
    42178, 46997, 40913, 29844, 19355, 9159, 10893, 30277, 42178, 52135, 62095, 50968,
    34119, 19853, 11897, 10143, 37654, 46997, 62095, 69248, 58002, 35317, 21416, 8987,
    7094, 25102, 40913, 50968, 58002, 54024, 31402, 17615, 9645, 4234, 19133, 29844,
    34119, 35317, 31402, 15631, 7908, 5892, 2437, 11538, 19355, 19853, 21416, 17615,
    7908, 8216, 749, 1195, 5180, 9159, 11897, 8987, 9645, 5892, 749, 1616,
    4594, 3026, 5907, 4494, 6102, 2714, 2408, 1186, 562, 3026, 5337, 9096,
    14693, 14011, 11768, 8751, 5218, 2417, 5907, 9096, 15061, 16657, 25921, 16897,
    16500, 9185, 4285, 4494, 14693, 16657, 24372, 29261, 24471, 16191, 11937, 5686,
    6102, 14011, 25921, 29261, 34366, 28177, 19370, 9016, 7431, 2714, 11768, 16897,
    24471, 28177, 26129, 16516, 9685, 4290, 2408, 8751, 16500, 16191, 19370, 16516,
    11597, 5847, 2651, 1186, 5218, 9185, 11937, 9016, 9685, 5847, 734, 1602,
    562, 2417, 4285, 5686, 7431, 4290, 2651, 1602, 401
  ]

def correctionCoefficient103 (a : CorrectionIndex) : Nat :=
  correctionCoefficientArray103[a.1.val * 81 + a.2.1.val * 9 + a.2.2.val]'(
    by change a.1.val * 81 + a.2.1.val * 9 + a.2.2.val < 729; omega)

def integerMonomial (i j k coefficient : Nat) :
    MvPolynomial SpectralVariable (ZMod 103) :=
  (coefficient : MvPolynomial SpectralVariable (ZMod 103)) *
    MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j * MvPolynomial.X 2 ^ k

def correctionPolynomial103 : MvPolynomial SpectralVariable (ZMod 103) :=
  ∑ a : CorrectionIndex,
    integerMonomial a.1.val a.2.1.val a.2.2.val (correctionCoefficient103 a)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem residual_inverse_polynomial_identity_lift :
    MvPolynomial.C 53 * residualPolynomial103 * inversePolynomial103 =
      1 + quotientQuintic103 0 * quotientX103 +
        quotientQuintic103 1 * quotientY103 +
        quotientQuintic103 2 * quotientZ103 +
        (103 : MvPolynomial SpectralVariable (ZMod 103)) * correctionPolynomial103 := by
  classical
  simp (config := { maxSteps := 10000000 }) [
    residualPolynomial103, inversePolynomial103, quotientQuintic103,
    quotientX103, quotientY103, quotientZ103, monomial,
    correctionPolynomial103, correctionCoefficient103,
    correctionCoefficientArray103, integerMonomial,
    residualCube103, residualCoeff103, inverseCube103, inverseCoeff103,
    flattenIndex, residualCoeffArray103, inverseCoeffArray103,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [MvPolynomial.C_eq_algebraMap, map_ofNat]
  ring

theorem polynomial_characteristic_103 :
    (103 : MvPolynomial SpectralVariable (ZMod 103)) = 0 := by
  change algebraMap (ZMod 103) (MvPolynomial SpectralVariable (ZMod 103))
      (103 : ZMod 103) = 0
  rw [show (103 : ZMod 103) = 0 by decide, map_zero]

theorem residual_inverse_polynomial_identity :
    MvPolynomial.C 53 * residualPolynomial103 * inversePolynomial103 =
      1 + quotientQuintic103 0 * quotientX103 +
        quotientQuintic103 1 * quotientY103 +
        quotientQuintic103 2 * quotientZ103 := by
  simpa only [polynomial_characteristic_103, zero_mul, add_zero] using
    residual_inverse_polynomial_identity_lift

end

end ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse
