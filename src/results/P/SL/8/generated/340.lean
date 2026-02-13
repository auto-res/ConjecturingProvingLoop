

theorem closure_interInterior_subset_inter_closure'
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`.
  have hxA : x ∈ closure A := by
    have hSub : A ∩ interior B ⊆ A := by
      intro y hy
      exact hy.1
    exact (closure_mono hSub) hx
  -- `A ∩ interior B` is also contained in `B` (because `interior B ⊆ B`).
  have hxB : x ∈ closure B := by
    have hSub : A ∩ interior B ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact (closure_mono hSub) hx
  exact And.intro hxA hxB