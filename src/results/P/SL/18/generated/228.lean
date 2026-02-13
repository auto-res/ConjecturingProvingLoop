

theorem interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First inclusion: into `interior (closure A)`.
  have hA :
      interior (closure (A ∩ interior B : Set X)) ⊆
        interior (closure A) := by
    apply interior_mono
    have : closure (A ∩ interior B : Set X) ⊆ closure A := by
      apply closure_mono
      exact Set.inter_subset_left
    exact this
  -- Second inclusion: into `interior (closure B)`.
  have hB :
      interior (closure (A ∩ interior B : Set X)) ⊆
        interior (closure B) := by
    apply interior_mono
    have : closure (A ∩ interior B : Set X) ⊆ closure B := by
      apply closure_mono
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact this
  exact ⟨hA hx, hB hx⟩