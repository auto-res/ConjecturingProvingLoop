

theorem Topology.dense_of_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) → Dense (A : Set X) := by
  intro h
  exact ((dense_iff_closure_eq (s := (A : Set X))).2 h)