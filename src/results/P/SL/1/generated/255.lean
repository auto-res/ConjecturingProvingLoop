

theorem Topology.dense_union_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense A → Dense (A ∪ B) := by
  intro hA
  have hclosure : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    simp [closure_union, hA.closure_eq]
  exact (dense_iff_closure_eq).2 hclosure