import Mathlib.Data.LazyList
import Std.Data.Rat.Basic

-- FRACTRAN Program
-- Complete Syntax of FRACTRAN
def FProg : Type := List Rat

-- sequence of states (run) of FRACTRAN Program and input
-- Complete Semantics of FRACTRAN
def FRun : Type := Int → Nat → Int

-- list of program states
def FRun' : Type := Int → LazyList Int

-- same as next but with the option monad
def next' (prog : FProg) (n : Int) : Option Int :=
  match prog with
  | []      => none
  | q :: qs => if Rat.isInt (q * n)
               then (q * n).num -- coercion
               else next' qs n

-- gets the number that when multiplied by a fraction in the FProg is integral
def next (prog : FProg) (n : Int) : Int :=
  match prog with
  | []      => 0
  -- | q :: qs => cond (Rat.isInt (q * n)) (q * n).num $ next qs n
  | q :: qs => (
    cond (Rat.isInt (q * n)) (q * n).num $ next qs n
  )

-- list version of runProg
unsafe def runProg' (prog : FProg) : FRun' :=
  fun z ↦ match (next' prog z) with
          | none   => LazyList.nil
          | some k => LazyList.cons k $ runProg' prog k -- coercion

-- computes the run of FRACTRAN program and input
-- Complete Implementation of FRACTRAN
def runProg (prog : FProg) : FRun :=
  fun z n ↦ match n with
            | Nat.zero   => z
            | Nat.succ k => next prog $ runProg prog z k
