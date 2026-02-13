

theorem Topology.P2_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) : Topology.P2 (⋃ i, A i) := by
  -- Each open set `A i` satisfies `P2`.
  have hA_P2 : ∀ i, Topology.P2 (A i) := by
    intro i
    exact Topology.isOpen_implies_P2 (X := X) (A := A i) (hA i)
  -- Apply the existing union lemma for `P2`.
  exact Topology.P2_iUnion (X := X) (A := A) hA_P2