

theorem Topology.P2_iff_P1_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P1 (X := X) A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2
  · intro _
    exact Topology.P2_of_dense_interior (X := X) (A := A) h_dense