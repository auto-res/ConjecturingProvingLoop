

theorem P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have hP2 : Topology.P2 (interior A) := P2_interior A
  exact P2_imp_P3 (A := interior A) hP2