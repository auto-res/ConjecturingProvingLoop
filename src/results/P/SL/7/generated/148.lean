

theorem Topology.P1_P2_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_dense_interior (A := A) h
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) h
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) h
  exact ⟨hP1, hP2, hP3⟩