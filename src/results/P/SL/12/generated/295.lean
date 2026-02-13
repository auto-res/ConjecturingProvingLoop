

theorem Topology.image_interior_subset_image_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    {A : Set X} :
    f '' interior (A : Set X) ⊆ f '' closure A := by
  intro y hy
  rcases hy with ⟨x, hx_int, rfl⟩
  -- From `x ∈ interior A` we obtain `x ∈ A`.
  have hxA : (x : X) ∈ A := interior_subset hx_int
  -- Hence `x ∈ closure A`.
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  exact ⟨x, hx_cl, rfl⟩