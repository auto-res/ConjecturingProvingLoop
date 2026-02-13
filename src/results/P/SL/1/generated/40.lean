

theorem Topology.P1_iUnion_interior {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (A : ι → Set X) : Topology.P1 (⋃ i, interior (A i)) := by
  -- First, show that the union of the interiors is an open set.
  have hOpen : IsOpen (⋃ i, interior (A i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  -- Apply `P1_of_isOpen` to conclude the desired result.
  exact Topology.P1_of_isOpen (A := ⋃ i, interior (A i)) hOpen