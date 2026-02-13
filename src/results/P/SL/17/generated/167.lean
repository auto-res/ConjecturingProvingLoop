

theorem Topology.P2_iUnion_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    Topology.P2 (Set.iUnion A) := by
  -- `P2` holds for every open set `A i`.
  have hP2 : ∀ i, Topology.P2 (A i) := fun i =>
    Topology.P2_of_isOpen (A := A i) (hOpen i)
  -- Use the existing union lemma for `P2`.
  exact Topology.P2_iUnion (A := A) hP2