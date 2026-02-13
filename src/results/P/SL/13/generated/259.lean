

theorem Topology.P2_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- `A` is open, hence it satisfies `P2`.
  have hPA : Topology.P2 (X := X) A :=
    isOpen_implies_P2 (X := X) (A := A) hA_open
  -- Combine the two `P2` hypotheses using the existing union lemma.
  exact Topology.P2_union (X := X) (A := A) (B := B) hPA hPB