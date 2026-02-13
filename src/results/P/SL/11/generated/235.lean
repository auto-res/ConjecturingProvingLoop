

theorem closure_interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  apply closure_mono
  exact interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)