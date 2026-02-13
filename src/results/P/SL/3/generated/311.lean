

theorem P2_union_of_isOpen_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  have hP2A : Topology.P2 (A : Set X) :=
    Topology.P2_of_isOpen (A := A) hA
  exact Topology.P2_union (A := A) (B := B) hP2A hB