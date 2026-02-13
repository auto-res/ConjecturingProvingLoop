

theorem frontier_closure_subset_closure_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure A) ⊆ closure (frontier A) := by
  intro x hx
  -- First, `frontier (closure A)` is contained in `frontier A`.
  have h₁ : frontier (closure A) ⊆ frontier A :=
    frontier_closure_subset_frontier (X := X) (A := A)
  -- Next, any point of `frontier A` lies in `closure (frontier A)`.
  have h₂ : frontier A ⊆ closure (frontier A) := by
    intro y hy
    exact subset_closure hy
  -- Combine the two inclusions to obtain the desired result.
  exact h₂ (h₁ hx)