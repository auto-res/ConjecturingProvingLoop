

theorem Topology.closure_interior_iUnion_eq_closure_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (A : ι → Set X)
    (hA : ∀ i, IsOpen (A i)) :
    closure (interior (⋃ i, A i)) = closure (⋃ i, A i) := by
  -- The union of the `A i` is open because each `A i` is open.
  have hOpen : IsOpen (⋃ i, A i) := by
    apply isOpen_iUnion
    intro i
    exact hA i
  -- For an open set `S`, its interior is itself.
  have hInt : interior (⋃ i, A i) = (⋃ i, A i) := hOpen.interior_eq
  -- Rewriting with `hInt` gives the desired equality.
  simpa [hInt]