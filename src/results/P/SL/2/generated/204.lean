

theorem Topology.dense_implies_interior_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A →
      interior (closure (interior (closure (A : Set X)))) = (Set.univ : Set X) := by
  intro hDense
  have h :=
    Topology.dense_interior_closure_eq_univ (A := A) hDense
  simpa [interior_univ] using congrArg interior h