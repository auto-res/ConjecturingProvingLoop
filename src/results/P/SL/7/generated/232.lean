

theorem Topology.closureInterior_eq_of_P1_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP1 : Topology.P1 A) : closure (interior A) = (A : Set X) := by
  exact (Topology.P1_closed_iff_closureInterior_eq (A := A) hA).1 hP1