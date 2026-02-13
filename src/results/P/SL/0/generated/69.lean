

theorem closure_interior_subset_closure_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (A : Set X) := by
  exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)