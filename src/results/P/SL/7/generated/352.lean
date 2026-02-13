

theorem Topology.interiorClosure_inter_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure (A ∩ B ∩ C)) ⊆
      interior (closure A) ∩ interior (closure B) ∩ interior (closure C) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hA : x ∈ interior (closure A) := by
    have hSub : closure (A ∩ B ∩ C) ⊆ closure A := by
      apply closure_mono
      intro y hy
      exact hy.1.1
    exact (interior_mono hSub) hx
  -- Membership in `interior (closure B)`
  have hB : x ∈ interior (closure B) := by
    have hSub : closure (A ∩ B ∩ C) ⊆ closure B := by
      apply closure_mono
      intro y hy
      exact hy.1.2
    exact (interior_mono hSub) hx
  -- Membership in `interior (closure C)`
  have hC : x ∈ interior (closure C) := by
    have hSub : closure (A ∩ B ∩ C) ⊆ closure C := by
      apply closure_mono
      intro y hy
      exact hy.2
    exact (interior_mono hSub) hx
  exact ⟨⟨hA, hB⟩, hC⟩