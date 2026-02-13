

theorem isClosed_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) ⊆ A) : IsClosed (A : Set X) := by
  have hEq : closure (A : Set X) = A := by
    apply le_antisymm
    · exact h
    · exact subset_closure
  simpa [hEq] using (isClosed_closure : IsClosed (closure (A : Set X)))