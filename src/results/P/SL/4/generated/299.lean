

theorem isClosed_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ⊆ A → IsClosed A := by
  intro h
  have hEq : closure A = A := subset_antisymm h subset_closure
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa [hEq] using hClosed