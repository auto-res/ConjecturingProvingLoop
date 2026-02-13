

theorem closure_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (A : Set X) ⊆ A := by
  set_option maxRecDepth 20000 in
  simpa [hA.closure_eq]