

theorem interior_closure_inter_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure B) := by
  -- First note that `A ∩ interior B ⊆ B`.
  have h_sub : A ∩ interior B ⊆ B := by
    intro x hx
    exact (interior_subset : interior B ⊆ B) hx.2
  -- Taking closures preserves inclusions.
  have h_closure : closure (A ∩ interior B) ⊆ closure B := closure_mono h_sub
  -- Applying `interior_mono` yields the desired inclusion.
  exact interior_mono h_closure