

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  apply closure_mono
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)