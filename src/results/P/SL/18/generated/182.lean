

theorem P3_union_of_dense_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) :
    Topology.P3 (A ∪ B) := by
  have hDenseUnion : Dense (A ∪ B : Set X) :=
    Topology.dense_union_left (A := A) (B := B) hDenseA
  exact Topology.P3_of_dense (A := A ∪ B) hDenseUnion