import Mathlib

namespace M8.TaggedStore
abbrev Tag := List Bool
abbrev Store := List (Tag × Bool)
def address (n : ℕ) : Tag := n.bits
def recordBits (r : Tag × Bool) : List Bool :=
  r.1.flatMap (fun b => [true,b]) ++ [false,r.2]
def tapeBits (s : Store) : List Bool := s.flatMap recordBits
-- A compared bit or end marker is one primitive Boolean comparison.
def compare : Tag → Tag → Bool × ℕ
  | [], [] => (true,1)
  | [], _::_ => (false,1)
  | _::_, [] => (false,1)
  | a::as, b::bs =>
    if a = b then let q := compare as bs; (q.1,q.2+1)
    else (false,1)
-- Each visited record is scanned in its explicit tagged encoding, then its
-- buffered tag is compared. One extra primitive advances/tests the cursor.
def read (key : Tag) : Store → Option Bool × ℕ
  | [] => (none,1)
  | r::rs =>
    let q := compare key r.1
    let charge := (recordBits r).length + q.2 + 1
    if q.1 then (some r.2,charge)
    else let rest := read key rs; (rest.1,charge+rest.2)
-- This denotes an in-place payload write at the first matching record. The
-- structural returned list is the post-state, not an allocated copy of tape.
def write (key : Tag) (bit : Bool) : Store → Store × ℕ
  | [] => ([],1)
  | r::rs =>
    let q := compare key r.1
    let charge := (recordBits r).length + q.2 + 1
    if q.1 then ((r.1,bit)::rs,charge)
    else let rest := write key bit rs; (r::rest.1,charge+rest.2)
def packFrom (start : ℕ) : List Bool → Store
  | [] => []
  | b::bs => (address start,b)::packFrom (start+1) bs
end M8.TaggedStore
