

theorem Topology.P3_iUnion_interior {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (A : ι → Set X) : Topology.P3 (⋃ i, interior (A i)) := by
  -- The union of interiors is an open set.
  have hOpen : IsOpen (⋃ i, interior (A i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := ⋃ i, interior (A i)) hOpen