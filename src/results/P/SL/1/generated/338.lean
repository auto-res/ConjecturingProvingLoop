

theorem Topology.closure_inter_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (A ∩ B) := hA.inter hB
  -- A closed set is equal to its closure.
  simpa [hClosed.closure_eq]