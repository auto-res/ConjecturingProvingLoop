

theorem Topology.closure_inter_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = A ∩ B := by
  have h_closed : IsClosed ((A ∩ B) : Set X) := hA_closed.inter hB_closed
  simpa using h_closed.closure_eq