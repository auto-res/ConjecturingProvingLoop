

theorem isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    IsOpen A :=
  ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3)