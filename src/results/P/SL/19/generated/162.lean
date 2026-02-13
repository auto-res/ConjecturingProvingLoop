

theorem Topology.closure_inter_eq_inter_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  simpa using (hA.inter hB).closure_eq