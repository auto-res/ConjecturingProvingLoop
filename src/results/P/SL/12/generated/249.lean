

theorem Topology.image_subset_closure_image_interior_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P1 (X := X) A) :
    f '' (A : Set X) ⊆ closure (f '' interior A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P1`, `x` lies in the closure of `interior A`.
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- Hence `f x` lies in `f '' closure (interior A)`.
  have hy_image : f x ∈ f '' closure (interior A) := ⟨x, hx_cl, rfl⟩
  -- Use continuity of `f` to pass from the image of a closure
  -- to the closure of an image.
  have h_subset : f '' closure (interior A) ⊆ closure (f '' interior A) :=
    image_closure_subset_closure_image (X := X) (Y := Y)
      (f := f) hf (A := interior A)
  exact h_subset hy_image