

theorem closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : closure (A ∩ B) ⊆ closure A := closure_mono Set.inter_subset_left
  have hB : closure (A ∩ B) ⊆ closure B := closure_mono Set.inter_subset_right
  exact And.intro (hA hx) (hB hx)