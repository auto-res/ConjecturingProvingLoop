

theorem P2_closed_iff_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  exact
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed).trans
      ((Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).symm)