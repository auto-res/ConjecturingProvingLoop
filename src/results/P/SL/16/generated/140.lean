

theorem Topology.denseInterior_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A ∧
      Topology.P2 (X := X) A ∧
      Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) h_dense
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h_dense
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P3_of_dense_interior (X := X) (A := A) h_dense
  exact ⟨hP1, hP2, hP3⟩