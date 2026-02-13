

theorem Topology.image_interior_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {A : Set X} :
    f '' interior A ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxInt, rfl⟩
  have : f x ∈ f '' A := ⟨x, interior_subset hxInt, rfl⟩
  exact subset_closure this