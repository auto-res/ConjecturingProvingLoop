

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  -- `Set.univ` is open, hence it satisfies `P1` by `isOpen_P1`.
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  exact Topology.isOpen_P1 (A := Set.univ) hOpen