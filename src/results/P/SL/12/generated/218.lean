

theorem Topology.closure_image_interior_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {A : Set X} :
    closure (f '' interior A) ⊆ closure (f '' A) := by
  -- The image of `interior A` is contained in the image of `A`.
  have h_image : (f '' interior A : Set Y) ⊆ f '' A := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, interior_subset hx, rfl⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_image