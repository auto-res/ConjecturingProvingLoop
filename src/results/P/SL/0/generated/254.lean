

theorem P2_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 (A ∪ interior (B : Set X)) := by
  intro hP2A
  have hOpenInt : IsOpen (interior (B : Set X)) := isOpen_interior
  exact
    (Topology.P2_union_right_of_open
      (X := X) (A := A) (B := interior (B : Set X))) hP2A hOpenInt