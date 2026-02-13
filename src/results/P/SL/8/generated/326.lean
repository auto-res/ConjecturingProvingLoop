

theorem closure_interior_closure_interior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  -- We already have the inclusion between the interiors.
  have h :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A)
  -- Taking closures preserves inclusions.
  exact closure_mono h