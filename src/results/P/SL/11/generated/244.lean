

theorem P3_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P3 (⋃ i, A i) := by
  -- Each `A i` is open and hence satisfies `P3`.
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => Topology.P3_of_open (A := A i) (hA i)
  exact Topology.P3_iUnion hP3