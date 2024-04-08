import FRACTRAN.Basic
import Mathlib.Tactic

open Rat -- Gives the /. infix notation for a /. b ↔ Rat.divInt a b

namespace fracs
def A := 17 /. 91
def B := 78 /. 85
def C := 19 /. 51
def D := 23 /. 38
def E := 29 /. 33
def F := 77 /. 29
def G := 95 /. 23
def H := 77 /. 19
def I := 1  /. 17
def J := 11 /. 13
def K := 13 /. 11
def L := 15 /. 2
def M := 1  /. 7
def N := 55 /. 1
end fracs

def prime_game_list := [fracs.A, fracs.B, fracs.C, fracs.D, fracs.E,
                        fracs.F, fracs.G, fracs.H, fracs.I, fracs.J,
                        fracs.K, fracs.L, fracs.M, fracs.N]
def prime_game := runProg prime_game_list 2

lemma prime_game_doesnt_halt (n : Nat) : prime_game n ≠ 0 := by
  sorry

-- This is much weaker than the actual prime game theorem (doesn't show that it
-- generates every prime, doesn't show they're in order of magnitude, etc).
-- TODO is this something we want to actually formalize?
theorem prime_game_primes (n p : Nat) (exception : n ≠ 2) (h : prime_game n = 2^p) : Nat.Prime p := by
  sorry
