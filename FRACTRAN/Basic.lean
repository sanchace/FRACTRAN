import Mathlib.Data.Rat.Defs

-- FRACTRAN Program
-- Complete Syntax of FRACTRAN
def FProg : Type := List Rat

-- sequence of states (run) of FRACTRAN Program and input
-- Complete Semantics of FRACTRAN
def FRun : Type := Int → Nat → Int

-- gets the number that when multiplied by a fraction in the FProg is integral
def next (prog : FProg) (n : Int) : Int :=
  match prog with
  | []      => 0
  -- | q :: qs => cond (Rat.isInt (q * n)) (q * n).num $ next qs n
  | q :: qs => (
    --cond (Rat.isInt (q * n)) (q * n).num $ next qs n
    if frac_divs : (↑ q.den ∣ n) then ((n / q.den) * q.num) else next qs n 
  )

-- computes the run of FRACTRAN program and input
-- Complete Implementation of FRACTRAN
def runProg (prog : FProg) : FRun :=
  fun z n ↦ match n with
            | Nat.zero   => z
            | Nat.succ k => next prog $ runProg prog z k

-- Compute the output of a FRACTRAN program, up to a certain depth
def evalUntil (k : Nat) (prog : FProg) (input : Int) : Option Int :=
  match k with
    | Nat.zero
      => none
    | Nat.succ j
      => cond (next prog input == 0) input $ evalUntil j prog (next prog input)
