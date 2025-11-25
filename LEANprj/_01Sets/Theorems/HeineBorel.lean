import LEANprj.defs
import LEANprj._02Sequences.Theorems.BolzanoWeierstrass
import LEANprj._02Sequences.Theorems.SubsequenceConvEq
import LEANprj._02Sequences.Theorems.UniquenessTheorem
import LEANprj._02Sequences.Theorems.ConvImpliesBdd

lemma construct_unbounded_sequence
    (M : Set ℝ)
    (hnot : ¬ BoundedSet M) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ M) ∧ (¬ BoundedSequence a) :=
by
  classical
  have : ∀ N : ℕ, ∃ m ∈ M, |m| ≥ N := by
    intro N
    by_contra hC
    push_neg at hC
    have : BoundedSet M := by
      unfold BoundedSet
      use N + 1
      constructor
      · linarith
      · intro m hmM
        calc
          |m| < (N : ℝ) := by exact hC m hmM
          _ < (N : ℝ) + 1 := by linarith
    exact hnot this
  choose a haM haBig using this
  use a
  constructor
  · intro n; exact (haM n)
  · unfold BoundedSequence
    push_neg
    intro K K_pos
    use Nat.ceil K
    have : (Nat.ceil K : ℝ) ≥ K := Nat.le_ceil K
    calc
      |(a (Nat.ceil K))| ≥ (Nat.ceil K : ℝ) := haBig (Nat.ceil K)
      _ ≥ K := this

theorem compact_implies_bounded {M : Set ℝ} : CompactSet M → BoundedSet M := by
  sorry

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
    obtain ⟨k, ⟨hk_inc, ⟨L, hL⟩⟩⟩ := BolzanoWeierstrass a ha_bdd
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
    ·




      sorry
    -- kompaktni -> uzavrena
    · intros a L hn ha_conv
      obtain ⟨k, hk_inc, l, hl, lM⟩ := compactM a hn
      have h_leqL : l = L := by
        have hk_conv' := SubsequenceConvEq ha_conv k hk_inc
        apply Uniqueness (Subsequence a k) l L hl hk_conv'
      rw [← h_leqL]
      exact lM
