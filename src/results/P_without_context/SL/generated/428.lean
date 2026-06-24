

theorem Topology.P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact fun x hx => interior_subset (hP2 hx)