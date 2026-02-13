

theorem Topology.interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A := by
    have hsub : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono hsub) hx
  have hxB : x ∈ interior B := by
    have hsub : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (interior_mono hsub) hx
  exact And.intro hxA hxB