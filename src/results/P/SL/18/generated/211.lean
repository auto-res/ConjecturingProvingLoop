

theorem P3_union_of_dense {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) (hDenseB : Dense (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  have hDenseUnion : Dense (A ∪ B : Set X) :=
    Topology.dense_union (A := A) (B := B) hDenseA hDenseB
  exact Topology.P3_of_dense (X := X) (A := A ∪ B) hDenseUnion