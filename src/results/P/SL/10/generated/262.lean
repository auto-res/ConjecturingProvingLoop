

theorem Topology.closure_interior_eq_univ_iff_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) ↔
      (Topology.P1 A ∧ closure A = Set.univ) := by
  constructor
  · intro h_cl_int
    have hP1 : Topology.P1 A :=
      Topology.P1_of_closure_interior_eq_univ (X := X) (A := A) h_cl_int
    have h_dense : closure A = (Set.univ : Set X) :=
      Topology.closure_eq_univ_of_closure_interior_eq_univ
        (X := X) (A := A) h_cl_int
    exact And.intro hP1 h_dense
  · rintro ⟨hP1, h_dense⟩
    exact
      Topology.closure_interior_eq_univ_of_P1
        (X := X) (A := A) hP1 h_dense