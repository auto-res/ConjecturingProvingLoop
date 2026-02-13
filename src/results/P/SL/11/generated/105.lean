

theorem P1_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P1 (⋃ i, A i) := by
  -- Each `A i` is open, hence satisfies `P1`.
  have hP1 : ∀ i, Topology.P1 (A i) := fun i =>
    Topology.P1_of_open (A := A i) (hA i)
  -- Apply the existing `P1`-union lemma.
  exact Topology.P1_iUnion hP1