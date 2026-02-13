

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `closure (interior A)` is contained in `closure A`
  have h : closure (interior A) ⊆ closure A := by
    exact closure_mono interior_subset
  -- Taking interiors preserves this inclusion
  exact interior_mono h