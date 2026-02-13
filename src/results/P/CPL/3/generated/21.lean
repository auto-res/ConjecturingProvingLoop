

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (closure A) := by
  -- From `hA` we get an equality of closures.
  have h_eq : closure (interior A) = closure A := (P1_iff_eq).1 hA
  intro x hx
  -- Rewrite `hx` using the equality.
  have hx' : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  -- Use monotonicity of `interior` and `closure`.
  have h_subset : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior A ⊆ interior (closure A) := by
      apply interior_mono
      exact subset_closure
    exact closure_mono h_int
  -- Conclude.
  exact h_subset hx'