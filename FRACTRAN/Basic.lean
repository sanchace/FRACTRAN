import Mathlib.Data.Rat.Defs

-- FRACTRAN Program
-- Complete Syntax of FRACTRAN
def FProg : Type := List Rat

-- Sequence of states (run) of FRACTRAN Program and input
-- Complete Semantics of FRACTRAN
def FRun : Type := Int → Nat → Int

-- Computes the next state
def next (prog : FProg) (n : Int) : Int :=
  match prog with
  | []      => 0
  | q :: qs => (
    if frac_divs : (↑ q.den ∣ n) then ((n / q.den) * q.num) else next qs n 
  )

-- Computes the run of FRACTRAN program and input
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
