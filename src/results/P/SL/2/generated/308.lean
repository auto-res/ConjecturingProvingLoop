

theorem Topology.closure_inter_closed_eq_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (A : Set X) → IsClosed (B : Set X) →
      closure (A ∩ B : Set X) = (A ∩ B : Set X) := by
  intro hClosedA hClosedB
  have hClosed : IsClosed (A ∩ B : Set X) := hClosedA.inter hClosedB
  simpa using hClosed.closure_eq