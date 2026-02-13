

theorem P3_union_right_dense {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (A : Set X) →
      closure (B : Set X) = (Set.univ : Set X) →
      Topology.P3 (A ∪ B) := by
  intro hP3A hDenseB
  have hP3B : Topology.P3 (B : Set X) :=
    Topology.P3_of_dense (A := B) hDenseB
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B