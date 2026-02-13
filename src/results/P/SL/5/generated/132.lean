

theorem closure_inter_closure_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  have hsubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
    closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  exact hsubset hx.1