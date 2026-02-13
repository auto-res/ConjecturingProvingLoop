

theorem Topology.P3_iUnion_isOpen {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hOpen : ∀ i, IsOpen (A i)) : Topology.P3 (Set.iUnion A) := by
  have hP3 : ∀ i, Topology.P3 (A i) := fun i =>
    Topology.P3_of_isOpen (A := A i) (hOpen i)
  exact Topology.P3_iUnion (A := A) hP3