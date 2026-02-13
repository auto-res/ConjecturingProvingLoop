

theorem isOpen_of_closed_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A := by
  exact (Topology.P3_closed_iff_open hA_closed).1 hP3