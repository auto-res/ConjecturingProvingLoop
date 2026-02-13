

theorem P1_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P1 A := by
  intro hDenseInt
  -- Density gives `closure (interior A) = univ`.
  have hClos :
      closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).1 hDenseInt
  -- Apply the existing lemma.
  exact Topology.P1_of_closure_interior_eq_univ (A := A) hClos