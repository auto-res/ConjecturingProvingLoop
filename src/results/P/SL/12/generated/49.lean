

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h1 : Topology.P2 (X := X) A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA
  have h2 : Topology.P3 (X := X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  exact h1.trans h2.symm