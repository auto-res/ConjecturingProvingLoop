

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P1 A := by
  exact (P2_implies_P1 (A := A)) (P2_subsingleton (A := A))