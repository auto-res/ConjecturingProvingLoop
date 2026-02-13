

theorem Topology.P3_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P3 (⋃ i, A i) := by
  -- Each open set `A i` satisfies `P3`.
  have hP3 : ∀ i, Topology.P3 (A i) := by
    intro i
    exact Topology.isOpen_implies_P3 (X := X) (A := A i) (hA i)
  -- Take the union over all indices.
  exact Topology.P3_iUnion (X := X) (A := A) hP3