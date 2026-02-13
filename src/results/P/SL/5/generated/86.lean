

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (Set.univ : Set X) := by
  have h_open : IsOpen (Set.univ : Set X) := isOpen_univ
  simpa using Topology.isOpen_implies_P2 (X := X) (A := Set.univ) h_open