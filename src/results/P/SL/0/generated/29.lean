

theorem univ_has_all_Ps {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  exact Topology.isOpen_has_all_Ps (X := X) (A := (Set.univ : Set X)) hOpen