

theorem Topology.P3_closure_iff_interior_closure_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) ↔ interior (closure A) = closure A := by
  have h₁ := Topology.P3_closure_iff_open_closure (X := X) (A := A)
  have h₂ := Topology.isOpen_closure_iff_interior_eq_self (X := X) (A := A)
  exact h₁.trans h₂