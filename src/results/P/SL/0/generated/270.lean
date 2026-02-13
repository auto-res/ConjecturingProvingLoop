

theorem P2_union_interior_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 B → Topology.P2 (interior (A : Set X) ∪ B) := by
  intro hP2B
  have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
  exact
    Topology.P2_union_left_of_open
      (X := X) (A := interior (A : Set X)) (B := B) hOpenInt hP2B