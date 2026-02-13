

theorem Topology.dense_interior_implies_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hDense
  have hEq : closure (A : Set X) = (Set.univ : Set X) :=
    Topology.dense_interior_implies_closure_eq_univ (A := A) hDense
  simpa [hEq] using (isOpen_univ : IsOpen (Set.univ : Set X))