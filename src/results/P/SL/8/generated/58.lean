

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : A ⊆ closure A)
  exact closure_mono h