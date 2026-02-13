

theorem interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, move from `interior (closure (interior A))` to `interior (closure A)`.
  have hx' : x ∈ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A) hx
  -- Any point of `interior (closure A)` belongs to the closure of `interior (closure A)`.
  have h_subset : interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  exact h_subset hx'