

theorem P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hP3
  exact (Topology.isOpen_implies_P1 (X := X) (A := A)) hOpen