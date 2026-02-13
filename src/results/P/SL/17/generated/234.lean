

theorem Topology.inter_interior_subset_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  -- The set `interior A ∩ interior B` is open.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- It is contained in `A ∩ B`.
  have hSubset : interior A ∩ interior B ⊆ A ∩ B := by
    intro y hy
    exact ⟨interior_subset hy.1, interior_subset hy.2⟩
  -- By the maximality of the interior, it is contained in `interior (A ∩ B)`.
  have hInterior : interior A ∩ interior B ⊆ interior (A ∩ B) :=
    interior_maximal hSubset hOpen
  exact hInterior hx