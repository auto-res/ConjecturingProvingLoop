

theorem closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : x ∈ closure A := (closure_mono (Set.inter_subset_left)) hx
  have hB : x ∈ closure B := (closure_mono (Set.inter_subset_right)) hx
  exact And.intro hA hB