

theorem P1_implies_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P2 (interior (A : Set X)) := by
  intro _
  -- `interior A` is open, hence it satisfies `P2`.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  exact
    (Topology.isOpen_implies_P2
        (X := X)
        (A := interior (A : Set X))) hOpen