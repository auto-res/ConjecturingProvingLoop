

theorem P1_union_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  have hA' : (A : Set X) ⊆ closure (interior (A ∪ B)) :=
    hA.trans (closure_mono (interior_mono Set.subset_union_left))
  have hB' : (B : Set X) ⊆ closure (interior (A ∪ B)) :=
    hB.trans (closure_mono (interior_mono Set.subset_union_right))
  exact Set.union_subset hA' hB'