import LEANprj.Sequences.definitions
noncomputable section
open Classical

variable (A : Set ℝ) (l₀ u₀ : ℝ)

-- chci si vytvorit pulleni intervalu, a aby ho rozeznavalo simp
@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

-- definuju krok puleni, beru bud levou nebo pravou cast, podle toho kde mam a ∈ A
def step (l u : ℝ) : ℝ × ℝ :=
  if _ : ∃ a : A, mid l u < a then (mid l u, u) else (l, mid l u)

-- definuju si posloupnost dvojic (lₙ, uₙ)
def luNext : ℕ → ℝ × ℝ
  | 0 => (l₀, u₀)
  | n+1 => step A (luNext n).1 (luNext n).2

-- zadefinuju si posloupnosti pro samostatne lₙ, uₙ
def lSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).1
def uSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).2

-- exsitence a jednoznacnost suprema (infima)
theorem exists_supremum (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : ∃ u : ℝ, ∀ a ∈ A, a < u): ∃ s : ℝ, IsSup A s := by
  obtain ⟨l₀, hl₀⟩ := hA
  obtain ⟨u₀, hu₀⟩ := hUpperBdd
  have h_l₀_leq_u₀ : l₀ ≤ u₀ := by exact le_of_lt (hu₀ l₀ hl₀)
  have lₙ_leq_uₙ : ∀ n : ℕ, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := by
    intro n
    induction' n with d hd
    · simp [lSeq, uSeq, luNext]
      exact h_l₀_leq_u₀
    · simp [lSeq, uSeq, luNext]
      let l_d := lSeq A l₀ u₀ d
      let u_d := uSeq A l₀ u₀ d
      let lu_d_next := step A l_d u_d
      change lu_d_next.1 ≤ lu_d_next.2
      sorry
  sorry









theorem exists_unique_infimum (A : Set ℝ) : ∃! i : ℝ, IsInf A i := by
  sorry

end
