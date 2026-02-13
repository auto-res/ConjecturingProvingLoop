

theorem Topology.P3_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P3 (X := X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Any open set satisfies `P3`.
  have hPB : Topology.P3 (X := X) B :=
    Topology.isOpen_subset_interiorClosure (X := X) (A := B) hB_open
  -- Combine the two `P3` hypotheses using the existing union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := B) hPA hPB