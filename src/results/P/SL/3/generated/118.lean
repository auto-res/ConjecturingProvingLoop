

theorem closure_inter_subset_inter_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  have hxA : (x : X) ∈ closure (A : Set X) := by
    have hSubset : ((A ∩ B) : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono hSubset) hx
  have hxB : (x : X) ∈ closure (B : Set X) := by
    have hSubset : ((A ∩ B) : Set X) ⊆ B := Set.inter_subset_right
    exact (closure_mono hSubset) hx
  exact And.intro hxA hxB