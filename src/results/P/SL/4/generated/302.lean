

theorem frontier_interior_subset_closure_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ closure (frontier A) := by
  intro x hx
  -- `frontier (interior A)` is contained in `frontier A`.
  have h_subset : frontier (interior A) ⊆ frontier A :=
    frontier_interior_subset_frontier (X := X) (A := A)
  -- Hence `x` belongs to `frontier A`.
  have hx_frontier : x ∈ frontier A := h_subset hx
  -- Every point of a set lies in the closure of that set.
  exact subset_closure hx_frontier