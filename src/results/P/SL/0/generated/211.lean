

theorem P3_implies_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P2 (interior (A : Set X)) := by
  intro _
  -- `interior A` is open, so it satisfies `P2`.
  exact
    (Topology.isOpen_implies_P2 (X := X)
      (A := interior (A : Set X))) isOpen_interior