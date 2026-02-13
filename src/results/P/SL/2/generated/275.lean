

theorem Topology.P3_iUnion_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P3 (s i)) →
      closure (interior (closure (⋃ i, s i : Set X))) = closure (⋃ i, s i : Set X) := by
  intro hP3
  have hP3Union : Topology.P3 (⋃ i, s i) :=
    Topology.P3_iUnion (s := s) hP3
  exact
    Topology.P3_implies_closure_interior_closure_eq_closure
      (A := ⋃ i, s i) hP3Union