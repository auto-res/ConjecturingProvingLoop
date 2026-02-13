

theorem interior_closure_interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  intro x hx
  -- First, note that `closure (interior A)` is contained in `closure A`
  have h_closure_subset : closure (interior A) ⊆ closure A := by
    have h_int_subset : interior A ⊆ A := interior_subset
    exact closure_mono h_int_subset
  -- Taking interiors preserves this inclusion
  have h_interiors : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  -- Apply the inclusion to the given point `x`
  exact h_interiors hx