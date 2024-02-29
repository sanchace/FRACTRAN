import Mathlib.Data.LazyList
import Mathlib.Tactic
import Std.Data.Rat.Basic
open Rat -- Gives the /. infix notation for a /. b ↔ Rat.divInt a b

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

--def n : Int := 2 ^ 3 * 3 ^ 7
--#eval n
--#eval LazyList.toList $ runProg' [(2 : Rat) / 3] n
--#eval runProg [(2 : Rat) / 3] n 7

def adder (a b : Nat) := runProg [2 /. 3] (2^a * 3^b)

-- runs the program 2/3 once on a multiple of 3 and returns it as a multiple of
lemma add_once {m : Int} : next [2 /. 3] (3 * m) = 2 * m := by
  -- unfold Rat.divInt
  rw [Rat.divInt_eq_div]
  unfold next
  simp
  repeat rw [
    ← mul_assoc,
    div_mul,
    div_self (by norm_num),
    div_one, two_mul,
    ← Int.cast_add,
    ← two_mul
  ]
  exact rfl

-- runs the adder program on input
lemma add_some {a b c : Nat} (h : c ≤ b) : adder a b c = 2 ^ (a + c) * 3 ^ (b - c) := by
  induction' c with c ih
  · rw [Nat.add_zero, Nat.sub_zero]
    exact rfl
  · conv =>
      congr
      · change next [2 /. 3] $ adder a b c
        rw [ih $ le_trans (Nat.le.step Nat.le.refl) h,
          ← Nat.succ_sub_succ b c,
          Nat.succ_sub h,
          pow_succ 3 _,
          ← mul_assoc,
          mul_comm _ 3]
      · rw [Nat.add_succ, pow_succ, mul_assoc]
    rw [mul_assoc 3 _]
    exact add_once

--
lemma add_correct (a b : Nat) : adder a b b = 2 ^ (a + b) := by
  convert add_some (le_refl b)
  rw [Nat.sub_self b, pow_zero, mul_one]

example (a b : Nat) : ((a == b) = true) ↔ (a = b) := by
  exact beq_iff_eq a b

lemma gcd_two_pow_x_three_eq_1 (x : Nat) : Int.gcd (2 ^ x) 3 = 1 := by
  refine Int.gcd_eq_one_iff_coprime.mpr ?_
  refine IsCoprime.pow_left ?H
  exact Int.gcd_eq_one_iff_coprime.mp rfl

-- proving that the adder will halt (be 0) at some point n > N
lemma add_halts {a n N : Nat} (h : n > N) (last : adder a N N = 2 ^ (a + N)) : adder a N n = 0 := by
  induction' n with n ih
  · exfalso
    exact (Nat.not_lt_zero N) h
  · unfold adder
    unfold runProg
    conv =>
      lhs
      rhs
      change adder a N n
    by_cases h' : n = N
    · rw [h', last]
      unfold next
      -- lean can't parse this unless it is a hypothesis
      have den_three : (2 /. 3).den = 3 := by
        rfl
      -- same with this
      have mul_divInt_ofInt : ((2 /. 3) * Rat.ofInt (2 ^ (a + N))) = (2 * 2 ^ (a + N)) /. 3 := by
        rw [
          Rat.mul_def,
        ]
        conv =>
          lhs
          conv =>
            lhs
            rw [den_three, Rat.ofInt_den, Nat.mul_one]
      conv =>
        lhs
        rw [
          ← Rat.ofInt_eq_cast (2 ^ (a + N)),
          mul_divInt_ofInt,
          ← pow_succ,
        ]
      -- this is the critical part as we show that the gcd 2 3 = 1
      -- this shows that in the case h'' is a contradiction
      have c : ((2 ^ (a + N + 1)) /. 3).den = 3 := by
        rw [Rat.den_mk]
        split
        · case inl three_eq_zero =>
          exfalso
          apply three_ne_zero at three_eq_zero
          exact three_eq_zero
        · case inr three_ne_zero =>
          conv =>
            lhs
            rhs
            apply gcd_two_pow_x_three_eq_1 (a + N + 1)
      unfold next
      unfold cond
      split
      · case _ h'' =>
        have three_neq_one : (3 == 1) = false := by
          rfl
        conv at h'' =>
          rw [
            Rat.isInt,
            c,
          ]
          conv =>
            lhs
            apply three_neq_one
          rw [Bool.coe_sort_false]
        exfalso
        exact h''
      · exact rfl
    · rw [ih ∘ Ne.lt_of_le' h' ∘ Nat.lt_succ.mp $ h]
      unfold next
      simp
      exact rfl


-- proof that the adder adds two numbers into the 2 register
-- and for all iterations after that produces 0
theorem adder_adds : ∀ a b : Nat, ∃ K : Nat, (adder a b K = 2^(a + b) ∧ ∀ n : Nat, n > K → adder a b n = 0) := by
  intro a b
  use b
  constructor
  · exact add_correct a b
  · intro n h
    exact add_halts h $ add_correct a b
