

theorem P2_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P2 (⋃ i, A i) := by
  -- Each `A i` is open, hence satisfies `P2`.
  have hP2 : ∀ i, Topology.P2 (A i) := fun i =>
    Topology.P2_of_open (A := A i) (hA i)
  -- Apply the existing union lemma for `P2`.
  exact Topology.P2_iUnion hP2