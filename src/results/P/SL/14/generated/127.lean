

theorem Topology.P2_union_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  -- Since `A` is open, it satisfies `P2`.
  have hA_P2 : Topology.P2 A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hA
  -- Apply the existing `P2_union` lemma.
  exact Topology.P2_union (X := X) (A := A) (B := B) hA_P2 hB