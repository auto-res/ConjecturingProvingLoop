

theorem Topology.closure_image_subset_closure_image_interior_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P1 (X := X) A) :
    closure (f '' A) ⊆ closure (f '' interior A) := by
  -- First, show that every point of `f '' A` already lies in
  -- `closure (f '' interior A)`.
  have h_subset : f '' A ⊆ closure (f '' interior A) := by
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    -- From `P1`, `x` is in the closure of `interior A`.
    have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
    -- Hence `f x` is in `f '' closure (interior A)`.
    have h_fx : f x ∈ f '' closure (interior A) := ⟨x, hx_cl, rfl⟩
    -- Use continuity to pass from `f '' closure _` to `closure (f '' _)`.
    have h_image :
        f '' closure (interior A) ⊆ closure (f '' interior A) :=
      Topology.image_closure_subset_closure_image
        (X := X) (Y := Y) (f := f) hf (A := interior A)
    exact h_image h_fx
  -- Taking closures of both sides gives the required inclusion.
  -- We use a small rewriting step to avoid the double‐closure on the right.
  have : closure (f '' A) ⊆ closure (closure (f '' interior A)) :=
    closure_mono h_subset
  simpa [closure_closure] using this