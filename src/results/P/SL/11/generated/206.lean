

theorem closure_iInter_eq_iInter {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i) = ⋂ i, A i := by
  have hClosed : IsClosed (⋂ i, A i) := by
    simpa using isClosed_iInter hA
  simpa using hClosed.closure_eq