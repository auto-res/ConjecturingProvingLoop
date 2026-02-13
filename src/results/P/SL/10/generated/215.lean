

theorem Topology.closure_image_interior_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {A : Set X} :
    closure (f '' interior A) ⊆ closure (f '' A) := by
  -- First, note the obvious inclusion `f '' interior A ⊆ f '' A`.
  have h_subset : f '' interior A ⊆ f '' A := by
    intro y hy
    rcases hy with ⟨x, hxInt, rfl⟩
    exact ⟨x, interior_subset hxInt, rfl⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset