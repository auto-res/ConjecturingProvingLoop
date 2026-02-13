

theorem Topology.P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _; exact Topology.P2_of_dense_interior (A := A) h_dense
  · intro hP2; exact Topology.P2_implies_P1 (A := A) hP2