

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X:=X) A) :
    Topology.P1 (X:=X) A := by
  intro x hx
  exact interior_subset (h hx)