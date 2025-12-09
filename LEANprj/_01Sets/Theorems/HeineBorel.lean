import LEANprj.defs
import LEANprj.lemmas
import LEANprj._02Sequences.Theorems.BolzanoWeierstrassConvSub
import LEANprj._02Sequences.Theorems.UniquenessSeq
import LEANprj._02Sequences.Theorems.ConvImpliesBdd

theorem compact_implies_bounded {M : Set ℝ} : CompactSet M → BoundedSet M := by
  intro h_compact
  by_contra h_unbdd
  unfold BoundedSet at h_unbdd
  push_neg at h_unbdd
  have exists_elem : ∀ n : ℕ, ∃ x ∈ M, |x| > n := by
    intro n
    have := h_unbdd (n + 1) (by linarith)
    rcases this with ⟨x, x_in_S, hx_mag⟩
    use x, x_in_S
    linarith
  let a : ℕ → ℝ := λ n => Classical.choose (exists_elem n)
  have a_in_S : ∀ n, a n ∈ M :=
    λ n => (Classical.choose_spec (exists_elem n)).1
  have a_large : ∀ n, |a n| > n :=
    λ n => (Classical.choose_spec (exists_elem n)).2
  rcases h_compact a a_in_S with ⟨k, k_inc, l,  h_conv, l_in_M⟩
  have h_conv : Convergent (Subsequence a k) := by use l
  have sub_bounded := ConvImpliesBdd h_conv
  rcases sub_bounded with ⟨K, K_pos, h_sub_bound⟩
  let n_large := Nat.ceil K + 1
  have h_boom : |Subsequence a k n_large| > K := by
    rw [Subsequence]
    calc |a (k n_large)| > k n_large := a_large (k n_large)
         _ ≥ n_large := by
            norm_cast
            induction n_large with
            | zero => exact Nat.zero_le _
            | succ n ih =>
              apply Nat.succ_le_of_lt
              apply lt_of_le_of_lt ih
              exact k_inc n
         _ > K := by
            simp [n_large]
            exact lt_of_le_of_lt (Nat.le_ceil K) (lt_add_one _)
  have h_bust := h_sub_bound n_large
  linarith



theorem HeineBorel (M : Set ℝ) : BoundedSet M ∧ ClosedSet M ↔ CompactSet M := by
  unfold BoundedSet ClosedSet CompactSet
  constructor
  -- omezena a uzavrena -> kompaktni
  · intro a
    cases' a with bddM clsM
    intro a ha
    obtain ⟨c, c_pos, c_bound⟩ := bddM
    have ha_bdd : BoundedSequence a := by
      unfold BoundedSequence
      use c
      refine ⟨c_pos, ?_⟩
      intro n
      have : a n ∈ M := ha n
      exact c_bound (a n) (ha n)
    obtain ⟨k, ⟨hk_inc, ⟨L, hL⟩⟩⟩ := BolzanoWeierstrassConvSub a ha_bdd
    have LinM : L ∈ M := by
      apply clsM (Subsequence a k) L
      · intro n
        exact ha (k n)
      · exact hL
    exact ⟨k, hk_inc, L, hL, LinM⟩
  -- kompaktni -> omezena a uzavrena
  · intro compactM
    constructor
    -- kompaktni -> omezena
    · exact compact_implies_bounded compactM
    -- kompaktni -> uzavrena
    · intros a L hn ha_conv
      obtain ⟨k, hk_inc, l, hl, lM⟩ := compactM a hn
      have h_leqL : l = L := by
        have hk_conv' := SubsequenceConvergesToSame ha_conv k hk_inc
        apply UniquenessSeq (Subsequence a k) l L hl hk_conv'
      rw [← h_leqL]
      exact lM
