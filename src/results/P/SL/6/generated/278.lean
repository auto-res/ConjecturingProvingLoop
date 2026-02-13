

theorem open_iff_all_Ps_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    IsOpen (A : Set X) ↔
      (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) := by
  calc
    IsOpen (A : Set X) ↔ Topology.P2 A :=
      (Topology.P2_iff_open_of_closed (A := A) hClosed).symm
    _ ↔ (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) :=
      (Topology.all_Ps_iff_P2_of_closed (A := A) hClosed).symm