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
  | q :: qs => cond (Rat.isInt (q * n)) (q * n).num $ next qs n

unsafe def runProg' (prog : FProg) : FRun' :=
  fun z ↦ match (next' prog z) with
          | none   => LazyList.nil
          | some k => LazyList.cons k $ runProg' prog k -- coercion

def runProg (prog : FProg) : FRun :=
  fun z n ↦ match n with
            | Nat.zero   => z
            | Nat.succ k => next prog $ runProg prog z k

--def n : Int := 2 ^ 3 * 3 ^ 7
--#eval LazyList.toList $ runProg' [(2 : Rat) / 3] n
--#eval runProg [(2 : Rat) / 3] n 7

def adder (a b : Nat) := runProg [(2 : Rat) / 3] (2^a * 3^b)

lemma add_once {m : Int} : next [(2 : Rat) / 3] (3 * m) = 2 * m := by
  conv =>
    lhs
    unfold next
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
        rw [(Int.cast_mul (Int.ofNat 2) m).symm]
        change ↑(2 * m)
      · rhs
        rw [← mul_assoc]
        conv =>
          lhs
          rw [div_mul, div_self (by norm_num), div_one]
        change (↑ (Int.ofNat 2)) * ↑ m
        rw [(Int.cast_mul (Int.ofNat 2) m).symm]
        change ↑(2 * m)
      · skip

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
            rw [(Nat.succ_sub_succ b c).symm, Nat.succ_sub h]
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
      sorry
    · rw [ih ∘ Ne.lt_of_le' h' ∘ Nat.lt_succ.mp $ h]
      sorry

theorem adder_adds : ∀ a b : Nat, ∃ K : Nat, (adder a b K = 2^(a + b) ∧ ∀ n : Nat, n > K → adder a b n = 0) := by
  intro a b
  use b
  constructor
  · exact add_correct a b
  · intro n h
    exact add_halts h $ add_correct a b
