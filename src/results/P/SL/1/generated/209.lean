

theorem Topology.P1_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior (A ∪ B)) := by
  -- The set `interior (A ∪ B)` is open, hence it satisfies `P1`.
  have hOpen : IsOpen (interior (A ∪ B)) := isOpen_interior
  exact Topology.P1_of_isOpen (A := interior (A ∪ B)) hOpen