

theorem Topology.closure_inter_eq_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  have h_closed : IsClosed (A ∩ B) := IsClosed.inter hA hB
  simpa using h_closed.closure_eq