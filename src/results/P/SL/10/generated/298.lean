

theorem Topology.closure_iInter_eq_iInter_of_isClosed
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i) = ⋂ i, A i := by
  classical
  have hClosed : IsClosed (⋂ i, A i) := isClosed_iInter hA
  simpa using hClosed.closure_eq