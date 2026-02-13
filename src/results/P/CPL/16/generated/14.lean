

theorem P1_eq_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 A → closure (interior A) = A := by
  intro hClosed hP1
  exact
    Set.Subset.antisymm
      (closure_minimal interior_subset hClosed)
      hP1