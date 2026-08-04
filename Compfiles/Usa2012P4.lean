/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import ProblemExtraction
public import Mathlib.Data.Int.NatAbs

problem_file { tags := [.Algebra] }

@[expose] public section

/-!
# USA Mathematical Olympiad 2007 P5
Find all functions f : ℤ₊ → ℤ₊ such that $f(n!) = f(n)! for all positive integers $n$ and such that $m - n$ divides $f(m) - f(n)$ for all distinct positive integers $m$, $n$.
-/

namespace USA2012P4
open Nat

def bounds (f: ℕ → ℕ): Prop := ∀n > 0, 0 < f n /-true by definition-/

snip begin


lemma factorial_fixpoints (n:ℕ) (n_pos: 0 < n) : n = (n)! ↔ (n = 1 ∨ n = 2) := by
  constructor
  · intro n_factorial
    by_cases hn : 2 < n
    · apply lt_factorial_self at hn
      linarith
    push Not at hn
    rw [Order.le_two_iff] at hn
    rw [pos_iff_ne_zero] at n_pos
    simp [n_pos] at hn
    assumption
  intro h
  rcases h with one | two
  · rw [one]
    simp
  rw [two]
  simp


lemma one_two {f: ℕ → ℕ} (hfac: ∀n, f ((n)!) = ((f n))!) :
  (f 1 = 1 ∨ f 1 = 2) ∧ (f 2 = 1 ∨ f 2 = 2) := by
  constructor
  · specialize hfac 1
    simp at hfac
    rw [factorial_fixpoints] at hfac
    · assumption
    rw [hfac]
    apply factorial_pos
  specialize hfac 2
  simp at hfac
  rw [factorial_fixpoints] at hfac
  · assumption
  rw [hfac]
  apply factorial_pos

lemma fac_even : ∀ i ≥ 3, Even (i)! := by
  intro i hi
  rw [even_iff_two_dvd]
  apply Nat.dvd_factorial
  · decide
  linarith

lemma fac_odd_iff_one (n:ℕ)(hn: 0 < n) : Odd (n)! ↔ n = 1 := by
  by_cases h : n < 2
  · rw [Order.lt_two_iff, le_one_iff_eq_zero_or_eq_one] at h
    rcases h with h | h
    · linarith
    constructor
    · simp [h]
    intro w
    rw [w]
    decide
  push Not at h
  constructor
  · intro h_odd
    by_contra! hn'
    by_cases h' : n ≥ 3
    · have fac_even' := fac_even n h'
      rw [← not_odd_iff_even] at fac_even'
      tauto
    push Not at h'
    have n2: n = 2 := by linarith
    have : Even (2 !) := by decide
    rw [n2] at h_odd
    rw [← not_odd_iff_even] at this
    tauto
  intro hn
  linarith



theorem le_two {f:ℕ → ℕ}(h_fac : ∀n,(f ((n)!) = (f n) !))(k: ℕ)(k_pos: 0 < k) (hk: k ≤ 2): f k = 1 ∨ f k = 2 ∨ f k = k := by

  rw [Order.le_two_iff] at hk
  obtain ⟨f1, f2⟩ := one_two h_fac
  rcases hk with h | h | h
  · linarith
  · rcases f1 with z | z
    · rw [← h] at z
      right;right;assumption
    rw [← h] at z
    right;left;assumption
  rcases f2 with z | z
  · rw [← h] at z
    left;assumption
  rw [← h] at z
  right;right;assumption


theorem main_claim {f:ℕ → ℕ}(hb: bounds f)(h_fac : ∀n,(f ((n)!) = (f n) !))(h_div: ∀m n :ℕ,(m:ℤ) - n ∣ ((f m - f n):ℤ)):
  ∀ k > 0, f k = 1 ∨ f k = 2 ∨ f k = k := by
  intro k  hk
  obtain ⟨f1, f2⟩ := one_two h_fac
  by_cases h : k < 3
  rw [← Nat.le_sub_one_iff_lt] at h
  simp at h
  exact le_two h_fac k hk h
  decide
  push Not at h

  rcases f2 with f2 | f2
  specialize h_div (k)! 2
  rw [f2, h_fac] at h_div
  have kf_even : Even ((k)! - 2) := by
    have fac_even_k := fac_even k h
    grind
  apply Even.trans_dvd at h_div
  norm_cast at h_div
  rw [Int.subNatNat_of_le] at h_div
  simp at h_div
  have fge1: ∀k, 1 ≤ (k)! := by
    intro k
    apply Nat.factorial_pos
  rw [← h_fac] at h_div
  have esub := Nat.even_sub (fge1 (f k))
  simp at esub
  rw [fac_odd_iff_one] at esub
  left
  rw [← esub, ← h_fac]
  assumption
  bound
  have : 0 < (f k)! := by apply Nat.factorial_pos (f k)
  linarith
  norm_cast
  rw [Int.subNatNat_of_le]
  simp
  assumption
  have : k ≤ (k)! := by apply Nat.self_le_factorial
  linarith

  rcases f1 with f1 | f1
  swap

  have f3 : f 3 = 2 := by
    specialize h_div (3)! 1
    by_cases hf3: f 3 ≥ 5
    have : 5 ∣ (f 3)! := by
      apply Nat.dvd_factorial
      decide
      assumption
    rw [f1] at h_div
    norm_num at h_div
    rw [show (6 = 3!) by decide] at h_div
    rw [h_fac] at h_div
    rw [dvd_sub_right] at h_div
    tauto
    norm_cast
    push Not at hf3
    have f_min : f 3 > 0 := by bound
    have f_opt : f 3 = 1 ∨ f 3 = 3 ∨ f 3 = 4 ∨ f 3 = 2 := by grind
    rcases f_opt with f3 | f3 | f3 | f3
    rw [h_fac,f3, f1] at h_div
    norm_cast at h_div
    rw [h_fac,f3, f1] at h_div
    norm_cast at h_div
    rw [h_fac,f3, f1] at h_div
    norm_cast at h_div
    assumption


  have : ∀m ≥ 3, f m = 2 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => assumption
    | succ w hm ih =>
      specialize h_div (w+1)! (w)!
      have fac_eq : ∀n, n * (n)! = (n+1)! - (n)! := by
        intro n
        rw [show ((n+1)! = (n+1)*(n)!) by apply Nat.factorial_succ]
        nth_rw 3 [show ((n)! = 1 * (n)!) by simp]
        generalize (n)! = q
        rw [add_mul]
        simp
      rw [h_fac,h_fac, ←Int.modEq_iff_dvd] at h_div
      norm_cast at h_div
      rw [Int.subNatNat_of_le] at h_div
      norm_cast at h_div
      specialize fac_eq w

      rw [← fac_eq,ih, Nat.factorial_two] at h_div
      apply Nat.ModEq.symm at h_div
      apply Nat.ModEq.of_mul_left at h_div
      have mod3 := h_div
      have div3 : 3 ∣ (w)! := by
        apply Nat.dvd_factorial
        decide
        lia
      apply Nat.ModEq.of_dvd div3 at mod3
      have : f (w+1) = 2 := by
        by_cases hf : 3 ≤ f (w+1)
        by_contra! hf'
        have le_fac:= Nat.self_le_factorial (f (w+1))
        have div3 : 3 ∣ (f (w+1))! := by
          apply Nat.dvd_factorial
          decide
          assumption
        rw [← Nat.modEq_zero_iff_dvd] at div3
        apply Nat.ModEq.symm at div3
        replace div3 := Nat.ModEq.trans div3 mod3
        apply Nat.ModEq.symm at div3
        rw [Nat.modEq_zero_iff_dvd] at div3
        tauto
        push Not at hf
        have f_opts : f (w+1) = 1 ∨ f (w+1) = 2 := by
          have : 0 < f (w+1) := by bound
          grind
        rcases f_opts with one | two
        rw [one] at mod3
        simp at mod3
        tauto
        assumption
      assumption
      apply Nat.factorial_le
      lia

  right
  left
  by_cases hk' : 3 ≤ k
  specialize this k
  simp at this
  apply this at hk'
  assumption
  push Not at hk'
  have k_opts : k = 1 ∨ k = 2 := by grind
  rcases k_opts with a | a
  rwa [a]
  rwa [a]
  























snip end
determine solution_set : Set (ℕ → ℕ) :=
  { fun _ ↦ 1, fun _ ↦ 2, fun n ↦ n }

problem usa2012_p4 (f: ℕ → ℕ) (n m : ℕ) (hn_pos : 0 < n)(hm_pos : 0 < m) :
  f ∈ solution_set ↔ f ((n)!) = (f n) ! ∧ m - n ∣ f m - f n := by
    sorry

end USA2012P4
