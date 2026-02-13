

theorem P2_iff_P3_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ :=
    (Topology.P2_iff_P3_and_closure_eq_closure_interior
      (X := X) (A := A))
  have h₂ :
      (Topology.P3 A ∧ closure A = closure (interior A)) ↔
        Topology.P3 A := by
    constructor
    · intro h; exact h.1
    · intro hP3; exact And.intro hP3 hEq
  exact h₁.trans h₂