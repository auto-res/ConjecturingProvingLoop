

theorem Topology.interior_iUnion_eq_iUnion_of_isOpen
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  -- The union of open sets is open.
  have h_open : IsOpen (⋃ i, A i : Set X) := isOpen_iUnion (fun i ↦ hA i)
  -- For an open set `U`, `interior U = U`.
  simpa [h_open.interior_eq]