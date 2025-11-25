import LEANprj.defs
import LEANprj._02Sequences.Theorems.BolzanoWeierstrass
import LEANprj._02Sequences.Theorems.SubsequenceConvEq
import LEANprj._02Sequences.Theorems.UniquenessTheorem

lemma construct_unbounded_sequence
    (M : Set ℝ)
    (hnot : ¬ BoundedSet M) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ M) ∧ (∀ N, ∃ n ≥ N, |a n| ≥ N) :=
by
  classical
  have : ∀ N > 0, ∃ m ∈ M, |m| ≥ N := by
    intro N
    by_contra hC
    -- hC říká: ∀ m∈M, |m| < N
    -- tedy množina je omezená konstantou N
    push_neg at hC
    have : BoundedSet M := by use N
    exact hnot this

  -- teď sestrojíme posloupnost a n tak, že |a n| ≥ n
  choose a haM haBig using this

  refine ⟨a, ?_, ?_⟩
  · intro n; exact (haM n)
  · intro N
    refine ⟨N, le_rfl, haBig N⟩

lemma unbounded_subsequence_contradiction
    {a : ℕ → ℝ}
    (ha_unbounded : ∀ N, ∃ n ≥ N, |a n| ≥ N)
    (hbounded_sub : ∀ n, |a n| ≤ 1000) :
    False :=
by
  -- vezmi N = 1001
  have := ha_unbounded 1001
  rcases this with ⟨n, hn, hbig⟩
  have hsmall := hbounded_sub n
  have : (1000 : ℝ) < 1001 := by decide
  have := le_trans hsmall (by decide)
  linarith


theorem HeineBorel (M : Set ℝ) : BoundedSet M ∧ ClosedSet M ↔ CompactSet M := by
  unfold BoundedSet ClosedSet CompactSet
  constructor
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
    obtain ⟨k, ⟨hk_inc, ⟨L, hL⟩⟩⟩ := BolzanoWeierstrass a ha_bdd
    have LinM : L ∈ M := by
      apply clsM (Subsequence a k) L
      · intro n
        exact ha (k n)
      · exact hL
    exact ⟨k, hk_inc, L, hL, LinM⟩
  · intro compactM
    constructor
    ·
      sorry
    · intros a L hn ha_conv
      obtain ⟨k, hk_inc, l, hl, lM⟩ := compactM a hn
      have h_leqL : l = L := by
        have hk_conv' := SubsequenceConvEq ha_conv k hk_inc
        apply Uniqueness (Subsequence a k) l L hl hk_conv'
      rw [← h_leqL]
      exact lM
