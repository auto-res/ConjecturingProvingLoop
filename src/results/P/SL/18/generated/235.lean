

theorem isOpen_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    IsOpen (closure (A : Set X)) := by
  have hEq : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  simpa [hEq] using (isOpen_univ : IsOpen (Set.univ : Set X))