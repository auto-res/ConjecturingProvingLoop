

theorem Topology.P1_iUnion_implies_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P1 (s i)) →
      closure (interior (⋃ i, s i : Set X)) = closure (⋃ i, s i : Set X) := by
  intro hP1
  -- First, the union itself satisfies `P1`.
  have hP1Union : Topology.P1 (⋃ i, s i) :=
    Topology.P1_iUnion (s := s) hP1
  -- Apply the characterisation of `P1` in terms of closures.
  exact
    Topology.P1_implies_closure_interior_eq_closure
      (A := ⋃ i, s i) hP1Union