

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) := by
  have h_open : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using Topology.isOpen_implies_P1 (X := X) (A := Set.univ) h_open