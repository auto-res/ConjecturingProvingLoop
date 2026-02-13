

theorem Topology.P2_union_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : IsOpen B) : Topology.P2 (A ∪ B) := by
  have hB_P2 : Topology.P2 B :=
    Topology.isOpen_implies_P2 (X := X) (A := B) hB
  exact Topology.P2_union (X := X) (A := A) (B := B) hA hB_P2