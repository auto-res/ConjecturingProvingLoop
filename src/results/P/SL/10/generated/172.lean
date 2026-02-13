

theorem Topology.closure_inter_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B) := hA.inter hB
  simpa using hClosed.closure_eq