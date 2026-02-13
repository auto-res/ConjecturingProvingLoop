

theorem closure_inter_interior_subset_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`, hence its closure is contained in `closure A`.
  have hA : closure (A ∩ interior B : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ interior B : Set X) ⊆ A)
  -- Likewise, `A ∩ interior B` is contained in `B`, so its closure is contained in `closure B`.
  have hB : closure (A ∩ interior B : Set X) ⊆ closure B := by
    have hSub : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact closure_mono hSub
  exact ⟨hA hx, hB hx⟩