

theorem closureInteriorClosureInterior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆ closure A := by
  -- We already have `interior (closure (interior A)) ⊆ closure A`.
  have h :
      interior (closure (interior A)) ⊆ closure A :=
    interior_closure_interior_subset_closure (X := X) (A := A)
  -- Taking closures preserves inclusions.
  simpa [closure_closure] using closure_mono h