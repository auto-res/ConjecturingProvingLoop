

theorem Topology.P1_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P1 (X:=X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P1 (X:=X) (A ∪ B) := by
  -- An open set automatically satisfies `P1`.
  have hPB : Topology.P1 (X:=X) B :=
    Topology.isOpen_subset_closureInterior (X:=X) (A:=B) hB_open
  -- Combine the two `P1` properties via the existing union lemma.
  exact Topology.P1_union (X:=X) (A:=A) (B:=B) hPA hPB