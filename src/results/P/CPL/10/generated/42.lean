

theorem exists_finite_P3 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, A.Finite ∧ Topology.P3 A := by
  refine ⟨(∅ : Set X), Set.finite_empty, ?_⟩
  exact Topology.P3_empty (X := X)