

theorem Topology.closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro z hz
      exact hz.1
    exact (closure_mono hSub) hx
  have hxB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro z hz
      exact hz.2
    exact (closure_mono hSub) hx
  exact And.intro hxA hxB