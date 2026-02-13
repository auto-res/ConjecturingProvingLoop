

theorem clopen_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A := by
  simpa using Topology.open_satisfies_all_Ps (A := A) hOpen