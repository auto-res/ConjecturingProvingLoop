

theorem P3_implies_P2_iff_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (Topology.P2 A ↔ closure A = closure (interior A)) := by
  intro hP3
  have h₁ :=
    (Topology.P2_iff_P3_and_closure_eq_closure_interior (X := X) (A := A))
  have h₂ :
      (Topology.P3 A ∧ closure A = closure (interior A)) ↔
        closure A = closure (interior A) := by
    constructor
    · intro h
      exact h.2
    · intro hEq
      exact And.intro hP3 hEq
  exact h₁.trans h₂