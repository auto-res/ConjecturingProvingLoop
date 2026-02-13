

theorem P2_iff_P3_and_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) ↔
      (Topology.P3 A ∧
        interior (closure (A : Set X)) = interior (closure (interior A))) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P2_implies_P3 (A := A) hP2
    have hEq :
        interior (closure (A : Set X)) =
          interior (closure (interior A)) :=
      Topology.P2_implies_interior_closure_eq (A := A) hP2
    exact And.intro hP3 hEq
  · rintro ⟨hP3, hEq⟩
    exact
      Topology.P3_and_interiors_equal_implies_P2
        (A := A) hP3 hEq