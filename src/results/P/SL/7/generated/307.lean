

theorem Topology.P1_P2_P3_of_dense_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure (interior A)) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interiorClosureInterior (A := A) h
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (A := A) hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (A := A) hP2
  exact ⟨hP1, hP2, hP3⟩