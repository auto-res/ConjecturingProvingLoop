

theorem Topology.P2_union_isClosed_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_closed : IsClosed B) (hB_P2 : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  -- From `P2 B` and closedness we know that `B` is open.
  have hB_open : IsOpen B :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := B) hB_closed hB_P2
  -- Apply the existing lemma for the union with an open set.
  exact Topology.P2_union_isOpen_right (X := X) (A := A) (B := B) hA hB_open