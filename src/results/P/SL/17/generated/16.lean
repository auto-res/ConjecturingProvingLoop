

theorem Topology.P_properties_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧
      Topology.P3 (Set.univ : Set X) := by
  simpa using
    (Topology.P_properties_of_isOpen (A := (Set.univ : Set X)) isOpen_univ)