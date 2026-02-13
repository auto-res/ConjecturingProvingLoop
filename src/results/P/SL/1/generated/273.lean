

theorem Topology.P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := (Set.univ : Set X)) hOpen)