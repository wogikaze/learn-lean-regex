import Regex.Core
import Regex.Set

open Regex

-- a+はaa*
def plus : Regex → Regex
  | r => cat r (star r)

-- a?はa|ε
def opt : Regex → Regex
  | r => alt r Eps

-- abcはcat (lit 'a') (cat (lit 'b') (cat (lit 'c') Eps))
def literal : String → Regex
  | s => s.toList.foldr (cat ∘ lit) Eps

-- a{10}はaa{9}
def exactly : Nat → Regex → Regex
  | 0, _ => Eps
  | (k+1), r => cat r (exactly k r)

-- a{5,}はa{5}a*
def atLeast : Nat → Regex → Regex
  | n, r => cat (exactly n r) (star r)

-- a{,5}は(aa{,4})?
def upTo : Nat → Regex → Regex
  | 0, _ => Eps
  | (k+1), r => opt (cat r (upTo k r))

def between : Nat → Nat → Regex → Regex
  | n, m, r => cat (exactly n r) (upTo (m - n) r)
