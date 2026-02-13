

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h1 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h2 : Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  exact h1.trans h2