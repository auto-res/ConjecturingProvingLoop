

theorem Topology.P2_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior (A ∪ B)) := by
  -- The set `interior (A ∪ B)` is open.
  have hOpen : IsOpen (interior (A ∪ B)) := isOpen_interior
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := interior (A ∪ B)) hOpen