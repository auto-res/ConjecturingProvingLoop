

theorem P3_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 (closure (A : Set X)) := by
  intro hDense
  have hCl : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  simpa [hCl] using (Topology.P3_univ (X := X))