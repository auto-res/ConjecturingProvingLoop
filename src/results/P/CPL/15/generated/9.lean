

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : interior A ⊆ interior (closure (interior A)) := by
  exact interior_subset.trans h