import LEANprj.defs


lemma StrictlyIncreasingSequenceN_ge_id (k : ℕ → ℕ) (hk : StrictlyIncreasingSequenceN k) :
  ∀ n, k n ≥ n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have : k (n + 1) ≥ k n + 1 := Nat.succ_le_of_lt (hk n)
    calc
      k (n + 1) ≥ k n + 1 := this
      _ ≥ n + 1 := by linarith

lemma LimitOrderLe (a b  : ℕ → ℝ) (p q : ℝ)
  (h₁ : a ≤ b) (h₂ : ConvergesTo a p) (h₃ : ConvergesTo b q) : p ≤ q := by
  by_contra hnle
  push_neg at hnle
  let ε := (p - q) / 2
  have ε_pos : ε > 0 := by have : p - q > 0 := by linarith;; dsimp [ε]; exact half_pos this
  obtain ⟨n₁, hn₁⟩ := h₂ ε ε_pos
  obtain ⟨n₂, hn₂⟩ := h₃ ε ε_pos
  let n₀ := max n₁ n₂
  have hn₁le : n₀ ≥ n₁ := le_max_left _ _
  have hn₂le : n₀ ≥ n₂ := le_max_right _ _
  specialize hn₁ n₀ hn₁le
  specialize hn₂ n₀ hn₂le
  specialize h₁ n₀
  rw [abs_lt] at hn₁ hn₂
  have : b n₀ < a n₀ := by calc a n₀
    _ > p - ε := by linarith
    _ = p - (p - q) / 2 := by dsimp [ε]
    _ = (p + q) / 2 := by ring
    _ = q + (p - q) / 2 := by ring
    _ = q + ε := by ring
    _ > b n₀ := by linarith
  linarith

lemma inc_le_of_le {a : ℕ → ℝ} (hinc : IncreasingSequence a) : ∀ {n m : ℕ}, n ≤ m → a n ≤ a m := by
  intro n m hnm
  refine Nat.le_induction (show a n ≤ a n from le_rfl) ?step m hnm
  intro k hk ih
  exact le_trans ih (hinc k)

lemma dec_le_of_le {a : ℕ → ℝ} (hdec : DecreasingSequence a) : ∀ {n m : ℕ}, n ≤ m → a n ≥ a m := by
  intro n m hnm
  refine Nat.le_induction (show a n ≥ a n from le_rfl) ?step m hnm
  intro k hk ih
  exact le_trans (hdec k) ih

lemma upperLowerBddIsBdd (a : ℕ → ℝ) (h_upper : UpperBoundedSequence a) (h_lower : LowerBoundedSequence a) : BoundedSequence a := by
rcases h_upper with ⟨u, hu⟩
rcases h_lower with ⟨l, hl⟩
let K := max (|l|) (|u|) + 1
use K
constructor
· have : 0 ≤ |l| := abs_nonneg l
  have : |l| ≤ max |l| |u| := le_max_left _ _
  linarith
· intro n
  rw [abs_le]
  constructor
  · have : -|l| ≤ l := neg_abs_le l
    have : |l| ≤ max |l| |u| := le_max_left _ _
    have : l ≤ a n := hl n
    linarith
  · have : u ≤ |u| := le_abs_self u
    have : |u| ≤ max |l| |u| := le_max_right _ _
    have : a n ≤ u := hu n
    linarith
