

theorem p2_imp_p1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (A := A) → Topology.P1 (X := X) (A := A) := by
  intro hP2 x hxA
  exact interior_subset (hP2 hxA)