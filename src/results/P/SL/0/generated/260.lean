

theorem P3_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 (A ∪ interior (B : Set X)) := by
  intro hP3A
  have hOpenInt : IsOpen (interior (B : Set X)) := isOpen_interior
  exact
    Topology.P3_union_right_of_open
      (X := X) (A := A) (B := interior (B : Set X)) hP3A hOpenInt