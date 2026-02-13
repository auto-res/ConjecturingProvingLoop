

theorem interior_closure_diff_subset_interior_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  -- `A \ B` is contained in `A`.
  have h_subset : A \ B ⊆ A := Set.diff_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure (A \ B) ⊆ closure A :=
    closure_mono h_subset
  -- Applying `interior` (a monotone operator) to both sides
  -- yields the desired inclusion.
  exact interior_mono h_closure_subset