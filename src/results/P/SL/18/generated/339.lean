

theorem dense_of_dense_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure (A : Set X))) → Dense (A : Set X) := by
  intro hDenseIntClos
  -- Translate density into a closure equality.
  have hEq :
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (closure (A : Set X)))).1 hDenseIntClos
  -- Apply the existing lemma that derives density of `A` from this equality.
  exact
    Topology.dense_of_closure_interior_closure_eq_univ
      (A := A) hEq