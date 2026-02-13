

theorem interior_closure_interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- `closure (interior A)` is contained in `closure (interior (closure A))`.
  have h : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (A := A)
  -- Taking interiors preserves this inclusion.
  exact interior_mono h