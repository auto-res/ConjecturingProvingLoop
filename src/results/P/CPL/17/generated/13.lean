

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P3 A := by
  exact (P2_implies_P3 (A := A) (P2_subsingleton (A := A)))