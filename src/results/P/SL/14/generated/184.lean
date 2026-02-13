

theorem Topology.P2_of_closureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 A := by
  intro hEq
  have hDense : Dense (interior A) :=
    (dense_iff_closure_eq (s := (interior A : Set X))).2 hEq
  exact Topology.P2_of_denseInterior (X := X) (A := A) hDense