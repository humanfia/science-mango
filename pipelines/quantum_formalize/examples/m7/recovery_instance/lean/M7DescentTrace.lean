import M5BinaryRecoveryAccepted

namespace M7.DescentTrace
structure Step where
  atPrefix : List Bool
  bit : Bool
  zero : ℤ
  one : ℤ
  deriving DecidableEq

def choose (z : ℤ) : Bool := if 0 < z then false else true

def trace (c : List Bool → ℤ) (p : List Bool) : ℕ → List Step
  | 0 => []
  | n+1 =>
    let z := c (p ++ [false])
    let o := c (p ++ [true])
    let b := choose z
    ⟨p,b,z,o⟩ :: trace c (p ++ [b]) n

def endpoint (p : List Bool) : List Step → List Bool
  | [] => p
  | s :: ss => endpoint (p ++ [s.bit]) ss

/-- Recomputes both child counts. The second component counts residual calls. -/
def check (c : List Bool → ℤ) (p : List Bool) : List Step → Bool × ℕ
  | [] => (true,0)
  | s :: ss =>
    let z := c (p ++ [false])
    let o := c (p ++ [true])
    if s.atPrefix == p && s.zero == z && s.one == o && s.bit == choose z then
      let t := check c (p ++ [s.bit]) ss
      (t.1,2+t.2)
    else (false,2)
end M7.DescentTrace
