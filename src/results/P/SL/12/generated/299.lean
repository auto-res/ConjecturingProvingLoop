

theorem Topology.closure_image_eq_closure_image_interior_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P1 (X := X) A) :
    closure (f '' A) = closure (f '' interior A) := by
  -- One inclusion is provided by an existing lemma.
  have h₁ :
      closure (f '' A) ⊆ closure (f '' interior A) :=
    Topology.closure_image_subset_closure_image_interior_of_P1
      (X := X) (Y := Y) (f := f) hf (A := A) hA
  -- The reverse inclusion follows from `interior A ⊆ A`.
  have h₂ :
      closure (f '' interior A) ⊆ closure (f '' A) := by
    -- First, relate the underlying images.
    have h_sub : (f '' interior A : Set Y) ⊆ f '' A := by
      intro y hy
      rcases hy with ⟨x, hx_int, rfl⟩
      exact ⟨x, interior_subset hx_int, rfl⟩
    -- Taking closures preserves inclusions.
    exact closure_mono h_sub
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂