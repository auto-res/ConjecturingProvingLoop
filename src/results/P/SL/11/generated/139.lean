

theorem P2_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P2 A := by
  -- For closed sets, `P2` and `P3` are equivalent.
  have hEquiv : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_closed (A := A) hClosed
  -- Apply the equivalence to turn the given `P3` into `P2`.
  exact (hEquiv.mpr hP3)