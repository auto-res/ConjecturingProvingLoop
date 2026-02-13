

theorem closure_inter_interior_subset_closure_inter_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure (A ∩ B) := by
  -- Since `interior B ⊆ B`, we have `A ∩ interior B ⊆ A ∩ B`.
  have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, interior_subset hx.2⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset