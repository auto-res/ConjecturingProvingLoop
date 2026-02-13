

theorem Topology.P2_iUnion_interior {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (A : ι → Set X) : Topology.P2 (⋃ i, interior (A i)) := by
  -- The union of the interiors is an open set.
  have hOpen : IsOpen (⋃ i, interior (A i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := ⋃ i, interior (A i)) hOpen