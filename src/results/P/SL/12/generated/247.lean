

theorem Topology.image_interior_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {A : Set X} :
    f '' interior (A : Set X) ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hx_int, rfl⟩
  have hxA : (x : X) ∈ (A : Set X) := interior_subset hx_int
  have h_im : (f x) ∈ f '' (A : Set X) := ⟨x, hxA, rfl⟩
  exact subset_closure h_im