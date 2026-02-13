

theorem closure_interior_eq_empty_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (∅ : Set X) → closure (interior A) = (∅ : Set X) := by
  intro h
  simpa [h, closure_empty]