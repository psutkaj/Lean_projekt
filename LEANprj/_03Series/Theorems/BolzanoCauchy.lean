import LEANprj.defs
import LEANprj._02Sequences.Theorems.CauchyEqConv

theorem BolzanoCauchy (a : ℕ → ℝ) : SeriesConvergent a ↔ CauchySequence (PartialSum a) := by
  rw [SeriesConvergent]
  unfold  SeriesConvergesTo
  rw [← Convergent]
  exact Iff.symm (CauchyEqConv (PartialSum a))

#print axioms BolzanoCauchy
-- (Assuming your previous definitions of PartialSum and CauchySequence are loaded)

/--
The "Image Version" of the condition.
This matches the visual formula: |a_{n+1} + ... + a_{n+p}| < ε
-/
def BolzanoCauchyCondition (a : ℕ → ℝ) :=
  ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, ∀ p : ℕ, |PartialSum a (n + p) - PartialSum a n| < ε

/--Proof that the Image Condition is equivalent to the Standard Cauchy Sequence.-/
theorem Image_Equivalent_To_Standard (a : ℕ → ℝ) :
  BolzanoCauchyCondition a ↔ CauchySequence (PartialSum a) := by
  constructor
  -- Direction 1: Image Condition → Standard Cauchy
  intro h_img ε hε
  obtain ⟨n₀, hn₀⟩ := h_img ε hε
  use n₀
  intro n m hnm
  -- We assume WLOG that m ≥ n to use the 'p' structure
  by_cases h_ord : n ≤ m
  · let p := m - n
    have hm : m = n + p := (Nat.add_sub_of_le h_ord).symm
    rw [hm]
    rw [abs_sub_comm]
    apply hn₀ n (le_of_lt hnm.1)
  · -- If n > m, we just flip them because |x - y| = |y - x|
    rw [abs_sub_comm]
    let p := n - m
    have hn : n = m + p := (Nat.add_sub_of_le (le_of_not_ge h_ord)).symm
    rw [hn]
    rw [abs_sub_comm]
    apply hn₀ m (le_of_lt hnm.2)

  -- Direction 2: Standard Cauchy → Image Condition
  intro h_cauchy ε hε
  obtain ⟨n₀, hn₀⟩ := h_cauchy ε hε

  -- Use the same n₀
  use n₀+1

  -- CRITICAL STEP: The intro order must match definition (∀ p n)
  intro n hn_ge p
  have hn_gt : n > n₀ := by linarith
  -- We need to feed (n + p) and (n) into the Cauchy hypothesis.
  -- We know n ≥ n₀. We must prove n + p > n₀.
  have h_np_gt : n + p > n₀ := by
    calc n + p ≥ n := by exact Nat.le_add_right n p
    _ > n₀ := by exact hn_ge

  -- Now we specialize the Cauchy hypothesis with m = n + p and n = n
  -- The hypothesis requires: (n+p) > n₀ AND n > n₀
  specialize hn₀ (n + p) n ⟨h_np_gt, hn_gt⟩

  -- The result matches exactly
  exact hn₀
