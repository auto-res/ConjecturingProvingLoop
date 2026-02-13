

theorem Topology.P3_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (Set.univ : Set X)) :
    Topology.P3 (X := X) A := by
  -- First, turn the hypothesis into the density statement `closure A = univ`.
  have h_closure : closure A = (Set.univ : Set X) :=
    (Topology.interior_closure_eq_univ_iff (X := X) (A := A)).1 h
  -- Conclude using the existing lemma for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A) h_closure