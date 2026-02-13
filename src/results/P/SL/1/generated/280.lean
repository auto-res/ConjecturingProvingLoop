

theorem Topology.interior_iUnion_eq_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (A : ι → Set X)
    (hA : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i) = ⋃ i, A i := by
  -- The union of the `A i` is open because each `A i` is open.
  have hOpen : IsOpen (⋃ i, A i) := by
    apply isOpen_iUnion
    intro i
    exact hA i
  -- For an open set `S`, `interior S = S`.
  simpa using hOpen.interior_eq