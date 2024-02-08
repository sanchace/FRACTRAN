import Mathlib.Data.LazyList
import Mathlib.Tactic

def FProg : Type := List Rat

def FRun : Type := Int → Nat → Int

def FRun' : Type := Int -> LazyList Int

def next' (prog : FProg) (n : Int) : Option Int :=
  match prog with
  | []      => none
  | q :: qs => if Rat.isInt (q * n)
               then (q * n).num -- coercion
               else next' qs n

def next (prog : FProg) (n : Int) : Int :=
  match prog with
  | []      => 0
  | q :: qs => if Rat.isInt (q * n)
               then (q * n).num
               else next qs n

unsafe def runProg' (prog : FProg) : FRun' :=
  fun z ↦ match (next' prog z) with
          | none   => LazyList.nil
          | some k => LazyList.cons k $ runProg' prog k -- coercion

def runProg (prog : FProg) : FRun :=
  fun z n ↦ match n with
  | Nat.zero => z
  | Nat.succ k => next prog $ runProg prog z k

def n : Int := 6
#eval LazyList.toList $ runProg' [Rat.mk' 2 3] n
#eval runProg [Rat.mk' 2 3] n 0

def adder (a b : Nat) := runProg [Rat.mk' 2 3] (2^a * 3^b)

theorem adder_adds : ∀ a b : Nat, ∃ K : Nat, (adder a b K = 2^(a + b) ∧ ∀ n : Nat, n > K → adder a b n = 0) := by
  intro a b
  use b
  constructor
  · sorry
  · intro n h
    sorry
