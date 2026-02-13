

theorem Topology.P1_iUnion_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    Topology.P1 (Set.iUnion A) := by
  -- Each `A i` is open, hence satisfies `P1`.
  have hP1 : ∀ i, Topology.P1 (A i) :=
    fun i => Topology.P1_of_isOpen (A := A i) (hOpen i)
  -- Apply the existing union lemma for `P1`.
  exact Topology.P1_iUnion (A := A) hP1