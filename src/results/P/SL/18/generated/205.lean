

theorem P2_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  have hP2B : Topology.P2 (B : Set X) := Topology.P2_of_open hOpenB
  exact Topology.P2_union (A := A) (B := B) hP2A hP2B