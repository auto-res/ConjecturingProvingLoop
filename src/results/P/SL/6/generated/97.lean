

theorem P2_iff_P3_and_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) ↔
      (Topology.P3 A ∧ closure (interior A) = closure A) := by
  constructor
  · intro hP2
    exact And.intro
      (Topology.P2_implies_P3 (A := A) hP2)
      (Topology.P2_implies_closure_interior_eq_closure (A := A) hP2)
  · rintro ⟨hP3, hEq⟩
    exact
      Topology.P3_and_closure_interior_eq_closure_implies_P2
        (A := A) hP3 hEq