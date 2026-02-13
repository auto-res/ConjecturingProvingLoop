

theorem Topology.P3_closure_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure A := by
  have h₁ :=
    Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  have h₂ :=
    Topology.isOpen_closure_iff_interior_eq_closure (X := X) (A := A)
  simpa using h₁.trans h₂