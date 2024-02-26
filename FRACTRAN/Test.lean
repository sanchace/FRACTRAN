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

def adder (a b : Nat) := runProg [Rat.divInt 2 3] (2^a * 3^b)

-- runs the program 2/3 once on a multiple of 3 and returns it as a multiple of
lemma add_once {m : Int} : next [Rat.divInt 2 3] (3 * m) = 2 * m := by
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
      · change next [Rat.divInt 2 3] $ adder a b c
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

-- proving that the adder will halt (be 0) at some point n > N
lemma add_halts {a n N : Nat} (h : n > N) (last : adder a N N = 2 ^ (a + N)) : adder a N n = 0 := by
  induction' n with n ih
  · exfalso
    exact (Nat.not_lt_zero N) h
  · unfold adder
    unfold runProg
    -- rw [adder] at ih
    conv =>
      lhs
      rhs
      change adder a N n
    by_cases h' : n = N
    · rw [h', last]
      unfold next
      -- rw [Rat.divInt_eq_div]
      -- simp
      repeat rw [
        -- div_mul_eq_mul_div,
        -- ENat.con_mul 2 (2 ^ (a + N)),
        -- ← Rat.cast_id (Rat.divInt 2 3),
        Rat.divInt_eq_div,
        -- ← Rat.intCast_mul,
        mul_comm,
        ← pow_succ'
      ]
      -- conv =>
      --   lhs
      --   lhs

      --   rw [
      --     ← Rat.ofInt_eq_cast (2 ^ (a + N)),
      --     Rat.mul_def,
      --   ]
      --   conv =>
      --     rhs
      --     lhs
      --     rhs
      --     rw [Rat.ofInt_den]

        -- have h''' : := by



      unfold next
      unfold cond
      split
      · case _ h'' =>
        exfalso
        rw [Rat.isInt] at h''
        rw [
          -- Rat.divInt_eq_div,
          -- Rat.intCast_mul,
          ← Rat.ofInt_eq_cast (2 ^ (a + N)),

          -- ← Rat.coe_int_div,
          -- Rat.mul_comm
        ] at h''
        rw [Rat.mul_def,] at h''
        conv at h'' =>
          lhs
          lhs
          conv =>
            rhs
            lhs
            conv =>
              rhs
              rw [Rat.ofInt_den]
            rw [Nat.mul_one]

        conv at h'' =>
          lhs




        -- unfold Rat.den at h''
        -- have den_not_one: Rat.normalize (_) ((Rat.divInt 2 3)) = Rat := by
          -- rw [Rat.ofInt_den]
        -- rw [int_one] at h''
        -- unfold Rat.ofInt at h''

        -- apply Rat.ofInt_den (2 ^ (a + N)) at h''
        -- conv =>
        --   lhs
        --   rhs
        --   change ↑ (2 / 3 * 2 ^ (a + N))

        -- unfold Rat.isInt at h''
        -- apply Rat.den_dvd _ 3 at h''
        -- refine false_of_true_eq_false (?_ (id last.symm))
        -- rw [beq_iff_eq _ 1] at h'' --inst mismatch instBEq vs instBEqNat ??
        -- apply Rat.mul_den at h''
        -- rw [pow_add, pow_one]
        -- rw [
          -- ← Rat.eq_num_of_isInt h'',
          -- Rat.coe_int_num
          -- ]
        -- apply?

        -- rw [Rat.divInt (2 ^ _) 3]
        -- rw [Rat.mul_den _ (1 / 3)] at h''

        sorry
      · exact rfl
    · rw [ih ∘ Ne.lt_of_le' h' ∘ Nat.lt_succ.mp $ h]
      unfold next
      simp
      exact rfl

-- lemma normalize_den {num den : Nat} : (Rat.normalize num).den = 1 := by
--   refine (Rat.den_eq_one_iff (Rat.normalize (↑num) 1)).mpr ?_
--   refine ?self.out.symm
--   apply?
--   sorry




-- proving that the adder will halt (be 0) at some point n > N
lemma add_halts' {a n N : Nat} (h : n > N) (last : adder a N N = 2 ^ (a + N)) : adder a N n = 0 := by
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
      repeat rw [div_mul_eq_mul_div, mul_comm, ← pow_succ']
      unfold next
      unfold cond
      split
      · case _ h'' =>

        -- exfalso
        -- rw [Rat.eq_num_of_isInt]
        rw [Rat.isInt, Nat.beq_eq_true_eq] at h''


        let g := Rat.divInt 2 3

        let den := Rat.isInt g
        unfold Rat.isInt at den

        -- rw [Rat.num_ne_zero_of_ne_zero]


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
