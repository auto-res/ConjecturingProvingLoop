

theorem P1_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  have hP1B : Topology.P1 B := Topology.P1_of_open hOpenB
  exact Topology.P1_union hP1A hP1B