

theorem Topology.closure_closed_left_inter_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) :
    closure A ∩ closure B = A ∩ closure B := by
  simpa [hA.closure_eq]