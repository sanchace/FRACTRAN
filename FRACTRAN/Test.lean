import Std.Data.Rat
import Mathlib.Data.LazyList

def FRACTRANprog : Type := List Rat

def FRACTRANrun : Type := Int → Nat → Int

def FRACTRANrun' : Type := Int -> LazyList Int

def next' (prog : FRACTRANprog) (n : Int) : Option Int :=
  match prog with
  | []      => none
  | q :: qs => if Rat.isInt (q * n)
               then Rat.floor $ q * n -- coercion
               else next' qs n

def next (prog : FRACTRANprog) (n : Int) : Int :=
  match prog with
  | []      => 0
  | q :: qs => if Rat.isInt (q * n)
               then Rat.floor $ q * n
               else next qs n

unsafe def runProg' (prog : FRACTRANprog) : FRACTRANrun' :=
  fun z ↦ match (next' prog z) with
          | none   => LazyList.nil
          | some k => LazyList.cons k $ runProg' prog k -- coercion

def runProg (prog : FRACTRANprog) : FRACTRANrun :=
  fun z n ↦ match n with
  | Nat.zero => z
  | Nat.succ k => next prog $ runProg prog z k

def n : Int := 6
#eval LazyList.toList $ runProg' [Rat.mk' 2 3] n
#eval runProg [Rat.mk' 2 3] n 0

def adder (a b : Nat) := runProg [Rat.mk' 2 3] (2^a * 3^b)

theorem adder_adds : ∀ a b : Nat, ∃ K : Nat, (adder a b K = 2^(a + b) ∧ ∀ n : Nat, n > N → adder a b n = 0) := by
  sorry
