import FRACTRAN.Basic
import Mathlib.Tactic

open Rat

-- Computes the sum of natural numbers
def adder (a b : Nat) := runProg [2 /. 3] (2^a * 3^b)

lemma add_once {m : Int} : next [2 /. 3] (3 * m) = 2 * m := by
  unfold next
  change (if frac_divs : 3 ∣ 3 * m then 3 * m / 3 * 2 else next [] (3 * m)) = 2 * m
  simp [Exists.intro m rfl, mul_comm]

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

-- Adder computes the right number every time (better than chatGPT)
lemma add_correct (a b : Nat) : adder a b b = 2 ^ (a + b) := by
  convert add_some (le_refl b)
  rw [Nat.sub_self b, pow_zero, mul_one]

-- Adder halts on every input
lemma add_halts {a n N : Nat} (h : n > N) (last : adder a N N = 2 ^ (a + N)) : adder a N n = 0 := by
  induction' n with n ih
  · exfalso
    exact (Nat.not_lt_zero N) h
  · have h : n ≥ N := Nat.lt_succ_iff.mp h
    rcases LE.le.eq_or_gt h with h | h
    · unfold adder
      unfold runProg
      unfold adder at last
      rw [h, last]
      unfold next
      unfold next
      have : ↑(2 /. 3).den = (3 : Int) := rfl
      rw [this]
      have (b : Nat) : ¬ ((3 : Int) ∣ (2 : Int) ^ b) :=
        (Prime.coprime_iff_not_dvd Int.prime_three).mp
        ∘ IsCoprime.pow_right
        ∘ Nat.isCoprime_iff_coprime.mpr
        $ Nat.coprime_of_lt_prime
          zero_lt_two
          (by norm_num)
          Nat.prime_three
      simp [this (a + N)]
    · apply ih at h
      unfold adder
      unfold runProg
      unfold adder at h
      rw [h]
      exact rfl

-- Adder behaves as expected: it correctly computing the sum and then
-- promptly halting
theorem adder_adds : ∀ a b : Nat, ∃ K : Nat, (adder a b K = 2^(a + b) ∧ ∀ n : Nat, n > K → adder a b n = 0) := by
  intro a b
  use b
  constructor
  · exact add_correct a b
  · intro n h
    exact add_halts h $ add_correct a b
