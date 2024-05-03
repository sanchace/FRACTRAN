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

-- Generalize the previous result to other adder implementations

example (a : ℤ) (h : b ≠ 0) : a * b / b = a := by
  exact Int.mul_ediv_cancel a h

variable (p q : Nat)
variable (pp : Nat.Prime p)
variable (pq : Nat.Prime q)
variable (pneq : p ≠ q)

def adder_general (a b : Nat) := runProg [p /. q] (p^a * q^b)


lemma add_once_general {m : Int}: next [p /. q] (q * m) = p * m := by
  unfold next
  have : ↑(↑p/.↑q).den = ↑q := by
    sorry
  rw [this]
  have : ↑(↑p/.↑q).num = ↑p := by
    sorry
  rw [this]
  simp
  rw [mul_comm]
  have : (↑q * m / ↑q) = m := by
    rw [mul_comm]
    apply Int.mul_ediv_cancel m _
    intro h
    have : q = 0 := Int.ofNat_eq_zero.mp h
    apply Nat.Prime.ne_zero pq
    assumption
  rw [this]

lemma add_some_general {a b c : Nat} (h : c ≤ b) : adder_general a b c = p ^ (a + c) * q ^ (b - c) := by
  sorry

lemma add_correct_general (a b : Nat) : adder_general a b b = p ^ (a + b) := by
  convert add_some_general p q (le_refl b)
  rw [Nat.sub_self, pow_zero, mul_one]

lemma add_halts_general {a n N : Nat} (h : n > N)
      (last : adder_general a N N = p ^ (a + N)) : adder_general a N n = 0 := by
  sorry

theorem adder_general_adds : ∀ a b : Nat, ∃ K : Nat,
      (adder_general a b K = p^(a + b) ∧ ∀ n : Nat, n > K → adder_general a b n = 0) := by
  intro a b
  use b
  constructor
  · exact add_correct_general p q a b
  · intro n h
    exact add_halts_general p h $ add_correct_general p q a b
