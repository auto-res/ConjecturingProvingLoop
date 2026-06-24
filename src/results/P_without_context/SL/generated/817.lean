

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  exact
    hP2.trans
      (interior_mono
        (closure_mono
          (interior_subset)))