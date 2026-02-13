

theorem Topology.interiorClosure_interInteriors_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Inclusion into `interior (closure (interior A))`.
  have hA : x ∈ interior (closure (interior A)) := by
    have hSub : closure (interior A ∩ interior B) ⊆ closure (interior A) := by
      apply closure_mono
      intro y hy
      exact hy.1
    have hSubInt : interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior A)) :=
      interior_mono hSub
    exact hSubInt hx
  -- Inclusion into `interior (closure (interior B))`.
  have hB : x ∈ interior (closure (interior B)) := by
    have hSub : closure (interior A ∩ interior B) ⊆ closure (interior B) := by
      apply closure_mono
      intro y hy
      exact hy.2
    have hSubInt : interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior B)) :=
      interior_mono hSub
    exact hSubInt hx
  exact And.intro hA hB