

theorem Topology.P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X:=X) A) : Topology.P1 (X:=X) A := by
  intro x hxA
  exact interior_subset (h hxA)