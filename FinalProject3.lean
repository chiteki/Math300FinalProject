import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ParityModular
import Library.Tactic.ModEq

math2001_init

/-
there are no integers a and b with b ≠ 0
such that a² = 2b². This is equivalent to the irrationality of √2,
since if √2 = a/b then a² = 2b².

using infinite descent,
  1. If a² = 2b², then a is even (since a² is divisible by 2).
  2. Writing a = 2j, substituting gives 4j² = 2b², so b² = 2j².
     Thus b is also even.
  3. Writing b = 2k, substituting gives j² = 2k²: a strictly
     smaller solution (|k| < |b|).
  4. By induction on |b| no such descent can continue forever,
     so b = 0 is the only solution.
-/

-- If n² is divisible by 2, then n is divisible by 2
theorem sq_even_imp_dvd (n : ℤ) (h : 2 ∣ n ^ 2) : 2 ∣ n := by
  obtain hn | hn := Int.even_or_odd n
  · exact hn
  · obtain ⟨k, hk⟩ := hn
    obtain ⟨j, hj⟩ := h
    have hn2 : n ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
      calc n ^ 2 = (2 * k + 1) ^ 2 := by rw [hk]
        _ = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    have hdvd : (2 : ℤ) ∣ 1 := by
      use j - (2 * k ^ 2 + 2 * k)
      calc 1 = n ^ 2 - 2 * (2 * k ^ 2 + 2 * k) := by addarith [hn2]
        _ = 2 * j - 2 * (2 * k ^ 2 + 2 * k) := by addarith [hj]
        _ = 2 * (j - (2 * k ^ 2 + 2 * k)) := by ring
    have hndvd : ¬ (2 : ℤ) ∣ 1 := by
      apply Int.not_dvd_of_exists_lt_and_lt
      use 0
      constructor <;> numbers
    contradiction

-- The equation a^2 = 2b^2 implies a is even (2 | a)
theorem eq_imp_a_even (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : 2 ∣ a := by
  have h1 : 2 ∣ a ^ 2 := by
    dsimp[(·∣·)]
    use b ^ 2
    exact h
  exact sq_even_imp_dvd a h1

-- The equation a^2 = 2b^2 implies b is also even (2 | b)
theorem eq_imp_b_even (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : 2 ∣ b := by
  obtain ⟨j, hj⟩ := eq_imp_a_even a b h
  have h1 : b ^ 2 = 2 * j ^ 2 := by
    have h2 : 2 * (2 * j ^ 2) = 2 * b ^ 2 := by
      calc 2 * (2 * j ^ 2) = (2 * j) ^ 2 := by ring
        _ = a ^ 2 := by rw [← hj]
        _ = 2 * b ^ 2 := h
    cancel 2 at h2
    exact h2.symm
  have h3 : 2 ∣ b ^ 2 := by
    dsimp[(·∣·)]
    use j ^ 2
    exact h1
  exact sq_even_imp_dvd b h3

-- Given a solution a^2 = 2b^2 with a = 2j and b = 2k, produces the smaller solution j^2 = 2k^2
theorem descent_step (a b j k : ℤ) (h : a ^ 2 = 2 * b ^ 2)
    (hj : a = 2 * j) (hk : b = 2 * k) : j ^ 2 = 2 * k ^ 2 := by
  have h1 : 2 * (2 * j ^ 2) = 2 * b ^ 2 := by
    calc 2 * (2 * j ^ 2) = (2 * j) ^ 2 := by ring
      _ = a ^ 2 := by rw [← hj]
      _ = 2 * b ^ 2 := h
  have h2 : 4 * j ^ 2 = 4 * (2 * k ^ 2) := by
    calc 4 * j ^ 2 = 2 * (2 * j ^ 2) := by ring
      _ = 2 * b ^ 2 := h1
      _ = 2 * (2 * k) ^ 2 := by rw [← hk]
      _ = 4 * (2 * k ^ 2) := by ring
  cancel 4 at h2

-- If b = 2k and b is nonzero, then the absolute value of k is strictly less than the absolute value of b
theorem natAbs_half_lt {b k : ℤ} (hb : b ≠ 0) (hk : b = 2 * k) :
    Int.natAbs k < Int.natAbs b := by
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    exact hb hk
  have hpos : 0 < Int.natAbs k := by
    rw [Int.natAbs_pos]
    exact hk0
  have hmul : Int.natAbs b = 2 * Int.natAbs k := by
    rw [hk, Int.natAbs_mul]
    rfl
  rw [hmul]
  calc Int.natAbs k = 1 * Int.natAbs k := by ring
    _ < 2 * Int.natAbs k := by
        have h2 : (1 : ℕ) < 2 := by numbers
        exact Nat.mul_lt_mul_of_pos_right h2 hpos

-- induction, if |b| is at most n and a^2 = 2b^2, then b = 0
theorem sqrt2_irr_core (n : ℕ) :
    ∀ a b : ℤ, Int.natAbs b ≤ n → a ^ 2 = 2 * b ^ 2 → b = 0 := by
  induction n with
  | zero =>
    intro a b hb h
    by_contra hne
    have h1 : 0 < Int.natAbs b := by
      rw [Int.natAbs_pos]
      exact hne
    have h2 : 0 < 0 := lt_of_lt_of_le h1 hb
    exact lt_irrefl 0 h2
  | succ n ih =>
    intro a b hbn h
    by_cases hb : b = 0
    · exact hb
    · obtain ⟨j, hj⟩ := eq_imp_a_even a b h
      obtain ⟨k, hk⟩ := eq_imp_b_even a b h
      have h' : j ^ 2 = 2 * k ^ 2 := descent_step a b j k h hj hk
      have hklt : Int.natAbs k < Int.natAbs b := natAbs_half_lt hb hk
      have hkle : Int.natAbs k ≤ n := by
        have h3 : Int.natAbs k < n + 1 := lt_of_lt_of_le hklt hbn
        exact Nat.le_of_lt_succ h3
      have hzero : k = 0 := ih j k hkle h'
      rw [hk, hzero, mul_zero]

-- if a^2 = 2b^2 then b = 0, meaning sqrt(2) is irrational
theorem sqrt2_irrational (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : b = 0 :=
  sqrt2_irr_core (Int.natAbs b) a b (le_refl _) h
