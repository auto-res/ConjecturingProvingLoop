

theorem Topology.interior_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    interior (A : Set X) = A := by
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
  simpa using hOpen.interior_eq