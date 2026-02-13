

theorem univ_has_all_P {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  simpa using
    (Topology.isOpen_has_all_P (X := X) (A := (Set.univ : Set X)) isOpen_univ)