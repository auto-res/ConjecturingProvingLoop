

theorem Topology.interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hA : x ∈ interior A := by
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro z hz; exact hz.1
    exact (interior_mono hSub) hx
  have hB : x ∈ interior B := by
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro z hz; exact hz.2
    exact (interior_mono hSub) hx
  exact And.intro hA hB