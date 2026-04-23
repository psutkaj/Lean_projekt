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

-- lemma inc_lt_of_ltN (k : ℕ → ℕ) (hk_inc : StrictlyIncreasingSequenceN k) : ∀ {n m : ℕ}, n < m → k n < k m := by
--     intro n m h
--     induction m, h using Nat.le_induction with
--     | base =>
--       exact hk_inc n
--     | succ m' _ ih =>
--       exact Nat.lt_trans ih (hk_inc m')

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

-- lemma DivInfUnbdd {a : ℕ → ℝ} (hdiv : DivergentToInf a) : ¬ BoundedSequence a := by
--   unfold BoundedSequence
--   unfold DivergentToInf at hdiv
--   push_neg
--   intro K K_pos
--   obtain ⟨n₀, hn₀⟩ := hdiv K K_pos
--   use n₀
--   specialize hn₀ n₀ (by linarith)
--   by_contra h
--   push_neg at h
--   have : |a n₀| ≥ a n₀ := by exact le_abs_self (a n₀)
--   have : |a n₀| > K := by
--     calc
--       |a n₀| ≥ a n₀ := this
--       _ > K := hn₀
--   linarith

-- lemma IncUnbddDivgToInf {a : ℕ → ℝ} (ha_inc : IncreasingSequence a) (ha_unbdd : ¬ BoundedSequence a) : DivergentToInf a := by
--   classical
--   intro M M_pos
--   have h_unbdd' : ∀ K > 0, ∃ n, |a n| > K := by
--     intro K K_pos
--     by_contra hfalse
--     push_neg at hfalse
--     have : BoundedSequence a := by
--       have : ∀ n : ℕ, a n ≤ |a n| := by exact fun n => le_abs_self (a n)
--       unfold BoundedSequence
--       refine ⟨K, K_pos, ?_⟩
--       intro n
--       exact hfalse n

--     exact ha_unbdd this
--   let K := M + |a 0| + 1
--   have K_pos : K > 0 := by
--     have : |a 0| ≥ 0 := abs_nonneg (a 0)
--     linarith
--   rcases h_unbdd' K K_pos with ⟨n0, hn0⟩

--   have hn0_pos : a n0 ≥ 0 := by
--     by_contra h
--     push_neg at h
--     rw [abs_of_neg h] at hn0
--     have : a n0 ≥ a 0 := inc_le_of_le ha_inc (Nat.zero_le n0)
--     have : a 0 ≥ -|a 0| := by exact neg_abs_le (a 0)
--     linarith

--   rw [abs_of_nonneg hn0_pos] at hn0

--   use n0
--   intro n hn_ge
--   have h_mono : a n ≥ a n0 := inc_le_of_le ha_inc hn_ge
--   have hK : K = M + |a 0| + 1 := rfl
--   have : |a 0| ≥ 0 := abs_nonneg (a 0)
--   linarith

-- lemma construct_unbounded_sequence
--     (M : Set ℝ)
--     (hnot : ¬ BoundedSet M) :
--     ∃ a : ℕ → ℝ, (∀ n, a n ∈ M) ∧ (¬ BoundedSequence a) :=
-- by
--   classical
--   have : ∀ N : ℕ, ∃ m ∈ M, |m| ≥ N := by
--     intro N
--     by_contra hC
--     push_neg at hC
--     have : BoundedSet M := by
--       unfold BoundedSet
--       use N + 1
--       constructor
--       · linarith
--       · intro m hmM
--         calc
--           |m| ≤ (N : ℝ) := by exact le_of_lt (hC m hmM)
--           _ ≤ (N : ℝ) + 1 := by linarith
--     exact hnot this
--   choose a haM haBig using this
--   use a
--   constructor
--   · intro n; exact (haM n)
--   · unfold BoundedSequence
--     push_neg
--     intro K K_pos
--     use Nat.ceil K + 1
--     have : (Nat.ceil K : ℝ) + 1 > K := lt_of_le_of_lt (Nat.le_ceil K) (lt_add_one _)
--     specialize haBig ((Nat.ceil K + 1) : ℕ)
--     push_cast at haBig
--     calc
--       |a (Nat.ceil K + 1)| ≥ ((Nat.ceil K + 1) : ℝ) := by exact haBig
--       _ = (Nat.ceil K : ℝ) + 1 := by simp
--       _ > K := this



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

-- lemma SubsequenceConvergesToSame {a : ℕ → ℝ} {L : ℝ}
--   (h_conv : ConvergesTo a L) (k : ℕ → ℕ) (hk : StrictlyIncreasingSequenceN k) :
--   ConvergesTo (Subsequence a k) L := by
--   intro ε hε
--   obtain ⟨n₀, hn₀⟩ := h_conv ε hε
--   use n₀
--   intro n hn
--   dsimp [Subsequence]
--   have h_idx : k n ≥ n₀ := le_trans hn (StrictlyIncreasingSequenceN_ge_id k hk n)
--   exact hn₀ (k n) h_idx

-- lemma Bounded_iff_Upper_and_Lower (a : ℕ → ℝ) :
--   BoundedSequence a ↔ UpperBoundedSequence a ∧ LowerBoundedSequence a := by
--   constructor
--   · intro h
--     obtain ⟨K, K_pos, hK⟩ := h
--     constructor
--     · use K; intro n; linarith [abs_le.mp (hK n)]
--     · use -K; intro n; linarith [abs_le.mp (hK n)]
--   · intro h
--     exact upperLowerBddIsBdd a h.1 h.2
