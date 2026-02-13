

theorem Topology.interior_inter_closures_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hA : x ∈ interior (closure (A : Set X)) := by
    have hSub : (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (A : Set X) := by
      intro y hy
      exact hy.1
    exact (interior_mono hSub) hx
  -- Membership in `interior (closure B)`
  have hB : x ∈ interior (closure (B : Set X)) := by
    have hSub : (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (B : Set X) := by
      intro y hy
      exact hy.2
    exact (interior_mono hSub) hx
  exact And.intro hA hB