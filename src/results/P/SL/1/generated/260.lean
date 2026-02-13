

theorem Topology.P3_union_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : Dense B) :
    Topology.P3 (A ∪ B) := by
  have h : Topology.P3 (B ∪ A) :=
    Topology.P3_union_of_dense_left (A := B) (B := A) hB
  simpa [Set.union_comm] using h