

theorem Topology.P2_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P2 (X := X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- `B` is open, hence it satisfies `P2`.
  have hPB : Topology.P2 (X := X) B :=
    (isOpen_implies_P2 (X := X) (A := B) hB_open)
  -- Combine the two `P2` hypotheses using the existing union lemma.
  exact Topology.P2_union (X := X) (A := A) (B := B) hPA hPB