

theorem closure_inter_interior_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure (A ∩ B) := by
  -- First, observe the straightforward set inclusion.
  have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, (interior_subset : interior B ⊆ B) hx.2⟩
  -- Taking closures preserves inclusions.
  exact closure_mono hSub