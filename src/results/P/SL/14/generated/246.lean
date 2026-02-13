

theorem Topology.closure_inter_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B : Set X) = (A ∩ B : Set X) := by
  -- The intersection of two closed sets is itself closed.
  have hClosed : IsClosed (A ∩ B : Set X) := IsClosed.inter hA hB
  -- A closed set is equal to its closure.
  simpa using hClosed.closure_eq