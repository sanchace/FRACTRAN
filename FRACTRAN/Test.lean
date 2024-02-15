import Mathlib.Data.LazyList
import Mathlib.Tactic

-- FRACTRAN Program
-- Complete Syntax of FRACTRAN
def FProg : Type := List Rat

-- sequence of states (run) of FRACTRAN Program and input
-- Complete Semantics of FRACTRAN
def FRun : Type := Int → Nat → Int

-- list of program states
def FRun' : Type := Int -> LazyList Int

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
  | q :: qs => cond (Rat.isInt (q * n)) (q * n).num $ next qs n

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

def adder (a b : Nat) := runProg [(2 : Rat) / 3] (2^a * 3^b)

lemma frac_denom_one_divides { f : Rat } (bnz : b ≠ 0) (h : f.den = 1) : b ∣ a := by
  sorry

-- runs the program 2/3 once on a multiple of 3 and returns it as a multiple of 2
lemma add_once {m : Int} : next [(2 : Rat) / 3] (3 * m) = 2 * m := by
  conv =>
    lhs
    unfold next
    simp
    conv =>
      congr
      · rhs
        rw [← mul_assoc]
        conv =>
          lhs
          rw [div_mul, div_self (by norm_num), div_one]
        change (↑ (Int.ofNat 2)) * ↑ m
        rw [← Int.cast_mul (Int.ofNat 2) m]
        change ↑(2 * m)
      · rhs
        rw [← mul_assoc]
        conv =>
          lhs
          rw [div_mul, div_self (by norm_num), div_one]
        change (↑ (Int.ofNat 2)) * ↑ m
        rw [← Int.cast_mul (Int.ofNat 2) m]
        change ↑(2 * m)
      · skip

-- runs the adder program on input
lemma add_some {a b c : Nat} (h : c ≤ b) : adder a b c = 2 ^ (a + c) * 3 ^ (b - c) := by
  induction' c with c ih
  · rw [Nat.add_zero, Nat.sub_zero]
    conv =>
      lhs
      change 2 ^ a * 3 ^ b
  · conv =>
      congr
      · change next [(2 : Rat) / 3] $ adder a b c
        rw [ih $ le_trans (Nat.le.step Nat.le.refl) h]
        rhs
        conv =>
          rhs
          conv =>
            rhs
            rw [← Nat.succ_sub_succ b c, Nat.succ_sub h]
          change 3 ^ (b - Nat.succ c) * 3
          rw [mul_comm]
        rw [← mul_assoc]
        conv =>
          lhs
          rw [mul_comm]
        rw [mul_assoc]
      · conv =>
          lhs
          conv =>
            rhs
            rw [Nat.add_succ]
          change 2 ^ (a + c) * 2
          rw [mul_comm]
        rw [mul_assoc]
    exact add_once

--
lemma add_correct (a b : Nat) : adder a b b = 2 ^ (a + b) := by
  convert add_some (le_refl b)
  conv =>
    rhs
    conv =>
      rhs
      conv =>
        rhs
        rw [Nat.sub_self b]
      change 1
    rw [mul_one]

example (a b : Nat) : ((a == b) = true) ↔ (a = b) := by
  exact beq_iff_eq a b

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
      simp
      conv =>
        lhs
        congr
        · rhs
          rw [div_mul_eq_mul_div, mul_comm, ← pow_succ']
          skip
        · rhs
          rw [div_mul_eq_mul_div, mul_comm, ← pow_succ']
          skip
        · unfold next
      unfold cond
      split
      · case pos.h_1 _ h'' =>
        exfalso
        unfold Rat.isInt at h''
        simp at h''
        have tnez : 3 ≠ 0 := by norm_num
        suffices ∃ n, 3 ∣ 2^n by
          -- Something something unique factorization
          sorry
        use a + N + 1
        apply frac_denom_one_divides tnez h''
      · exact rfl
    · rw [ih ∘ Ne.lt_of_le' h' ∘ Nat.lt_succ.mp $ h]
      unfold next
      simp
      conv =>
        skip

-- proof that the adder adds two numbers into the 2 register
-- and for all iterations after that produces 0
theorem adder_adds : ∀ a b : Nat, ∃ K : Nat, (adder a b K = 2^(a + b) ∧ ∀ n : Nat, n > K → adder a b n = 0) := by
  intro a b
  use b
  constructor
  · exact add_correct a b
  · intro n h
    exact add_halts h $ add_correct a b
