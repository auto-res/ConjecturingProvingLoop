

theorem Topology.image_interior_closure_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' interior (closure A) ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxIntClA, rfl⟩
  -- From `hxIntClA : x ∈ interior (closure A)`, deduce `x ∈ closure A`.
  have hxClA : x ∈ closure A := interior_subset hxIntClA
  -- Apply the existing inclusion for images of closures.
  have h_image_closure :=
    Topology.image_closure_subset_closure_image
      (X := X) (Y := Y) (f := f) hf (A := A)
  -- Since `f x ∈ f '' closure A`, the desired conclusion follows.
  exact h_image_closure ⟨x, hxClA, rfl⟩