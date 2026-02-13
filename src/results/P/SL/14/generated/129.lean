

theorem Topology.P1_union_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : IsOpen B) : Topology.P1 (A ∪ B) := by
  -- Since `B` is open, it satisfies `P1`.
  have hB_P1 : Topology.P1 B :=
    Topology.isOpen_implies_P1 (X := X) (A := B) hB
  -- Apply the existing `P1_union` lemma.
  exact Topology.P1_union (X := X) (A := A) (B := B) hA hB_P1