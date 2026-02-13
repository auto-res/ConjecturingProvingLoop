

theorem Topology.interior_union_interior_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∪ interior B) = interior A ∪ interior B := by
  -- `interior A` and `interior B` are open, hence their union is open.
  have hOpen : IsOpen ((interior A ∪ interior B) : Set X) := by
    exact (isOpen_interior.union isOpen_interior)
  -- For an open set `S`, we have `interior S = S`.
  simpa [hOpen.interior_eq]