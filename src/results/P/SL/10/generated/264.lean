

theorem Topology.closure_image_preimage_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set Y) :
    closure (f '' (f ⁻¹' A)) ⊆ closure A := by
  -- First, prove the basic inclusion between the sets.
  have h_subset : f '' (f ⁻¹' A) ⊆ A := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_subset