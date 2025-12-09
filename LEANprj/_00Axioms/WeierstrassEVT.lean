import LEANprj.defs

axiom WeierstrassEVT
  (f : ℝ → ℝ) (a b : ℝ)
  (h_ab : a ≤ b)
  (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  (FunctionBddOnSet Int f) ∧
  (∃ M ∈ Int, ∀ x ∈ Int, f x ≤ f M) ∧
  (∃ m ∈ Int, ∀ x ∈ Int, f m ≤ f x)
