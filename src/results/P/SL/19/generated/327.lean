

theorem Topology.closure_closed_right_inter_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure A ∩ closure B = closure A ∩ B := by
  simpa [Set.inter_comm, Set.inter_left_comm] using
    (Topology.closure_closed_left_inter_eq (X := X) (A := B) (B := A) hB)