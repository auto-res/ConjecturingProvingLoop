

theorem Topology.P1_union_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  have hA_P1 : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA_open
  exact Topology.P1_union (X := X) (A := A) (B := B) hA_P1 hB