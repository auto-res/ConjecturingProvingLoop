

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    have hsubset : (A ∩ B) ⊆ A := Set.inter_subset_left
    exact (closure_mono hsubset) hx
  have hxB : x ∈ closure B := by
    have hsubset : (A ∩ B) ⊆ B := Set.inter_subset_right
    exact (closure_mono hsubset) hx
  exact And.intro hxA hxB