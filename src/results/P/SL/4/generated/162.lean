

theorem interior_closure_diff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  intro x hx
  -- `A \ B` is contained in `A`.
  have h_sub : (A \ B : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- Taking closures and then interiors preserves inclusions.
  have h_incl :
      interior (closure (A \ B)) ⊆ interior (closure A) :=
    interior_mono (closure_mono h_sub)
  exact h_incl hx