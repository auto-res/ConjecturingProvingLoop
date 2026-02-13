

theorem Topology.P3_union_left_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- From the density of `interior A`, deduce that `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (X := X) (A := A) h_dense
  -- Apply the existing lemma for sets whose closure is the whole space.
  exact
    Topology.P3_union_left_dense (X := X) (A := A) (B := B) h_closure_univ