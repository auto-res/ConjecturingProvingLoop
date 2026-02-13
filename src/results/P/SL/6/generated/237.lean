

theorem interior_closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ closure B) : Set X)) ⊆ interior (closure A) := by
  intro x hx
  -- Since `A ∩ closure B ⊆ A`, their closures satisfy the same inclusion.
  have hSub : closure ((A ∩ closure B) : Set X) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  -- Monotonicity of `interior` gives the desired inclusion.
  exact (interior_mono hSub) hx