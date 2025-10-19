import Mathlib

-- uvod do posloupnosti

-- omezenost
def LowerBoundedSequence (a : ℕ → ℝ) := ∃ l : ℝ, ∀ n : ℕ, a n > l
def UpperBoundedSequence (a : ℕ → ℝ) := ∃ u : ℝ, ∀ n : ℕ, a n < u
def BoundedSequence (a : ℕ → ℝ) := ∃ K > 0, ∀ n : ℕ, |a n| < K

-- monotonie
def IncreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≥ a n
def StrictlyIncreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) > a n
def DecreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≤ a n
def StrictlyDecreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) < a n

example (a : ℕ → ℝ) (c : ℝ) (h : ∀ n : ℕ, a n = c) : BoundedSequence a := by
  unfold BoundedSequence
  use |c| + 1
  constructor
  linarith [abs_nonneg c]
  intro n
  rw [h]
  linarith

example (a : ℕ → ℝ) (c : ℝ) (h: ∀ n : ℕ, a n = c ∨ a n = -c) : BoundedSequence a := by
  unfold BoundedSequence
  use |c| + 1
  constructor
  linarith [abs_nonneg c]
  intro n
  cases h n with
  | inl hc => simp [hc]
  | inr hcn =>
    simp [hcn]

example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = n) : LowerBoundedSequence a ∧ ¬ UpperBoundedSequence a ∧ StrictlyIncreasingSequence a := by
  constructor
  unfold LowerBoundedSequence
  use -1
  intro n
  rw [ha]
  linarith
  constructor
  unfold UpperBoundedSequence
  -- zneguji vyraz
  contrapose!
  intro h u
  simp [ha]
  -- vim, ze ∀ u ∃ n : u ≤ n
  -- pro dk, ze neni omezena pouziju n = ⌈u⌉
  use (Int.ceil u).toNat
  -- vime, ze u ≤ ⌈u⌉
  have h₁ : u ≤ (Int.ceil u) := by exact Int.le_ceil u
  -- a potrebuju ukazat, ze ⌈u⌉ ≤ ⌈u⌉.toNat, abych mohl nasledne vyuzit tranzitivitu
  have h₂ : (Int.ceil u) ≤ ↑((Int.ceil u).toNat) := by
    -- dokazeme po castech napred pro 0 ≤ ⌈u⌉
    by_cases hpos : 0 ≤ Int.ceil u
      -- pro tento pripad vime, ze ↑⌈u⌉,toNat = ⌈u⌉, a pak trivialne
    · have : ↑((Int.ceil u).toNat) = Int.ceil u := by
        exact Int.toNat_of_nonneg hpos
      rw [this]
      -- a pro 0 ≥ ⌈u⌉ vime, ze ⌈u⌉.toNat = 0, protoze Nat cisla nemuzou byt mensi
    · have : (Int.ceil u).toNat = 0 := by
        simp_all only [not_false_eq_true, not_le, Int.toNat_eq_zero]
        linarith
      rw [this]
      exact Int.le_of_not_le hpos
  -- ted uz mame dokazane potrebne kroky k uziti tranzitivity pred ↑⌈u⌉
  trans ↑⌈u⌉
  · exact h₁
  · norm_cast
  unfold StrictlyIncreasingSequence
  intro n
  rw [ha, ha]
  norm_cast
  linarith


example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = (n / (n + 1))) : BoundedSequence a := by
  unfold BoundedSequence
  use 1
  constructor
  linarith
  intro n
  rw [ha]
  -- chci ukazat ze jmenovatel je pozitivni
  have denom_pos : 0 < (n + 1 : ℝ) := by
    norm_cast
    linarith
  -- chci ukazat ze citatel je mensi nee jmenovatel abych mohl ukaza ze n / n + 1 < 1
  have num_lt_denom : (n : ℝ) < (n + 1 : ℝ) := by
    linarith
  -- chci ukazat, ze n / n + 1 < 1
  have : (n : ℝ) / (n + 1 : ℝ) < 1 := by
    exact (div_lt_one₀ denom_pos).mpr num_lt_denom
  -- ukazu, ze vyraz je nezaporny
  have nonneg : 0 ≤ (n : ℝ) / (n + 1 : ℝ) := div_nonneg (by norm_cast; apply Nat.cast_nonneg) (le_of_lt denom_pos)
  -- a diky tomu abs vyrazu = vyraz
  have h : |(n : ℝ) / (n + 1 : ℝ)| = (n : ℝ) / (n + 1 : ℝ) := abs_of_nonneg nonneg
  rw [h]
  exact this
