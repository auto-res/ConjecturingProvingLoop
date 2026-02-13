

theorem Topology.P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior A)) ↔
      Topology.P3 (X := X) (closure (interior A)) := by
  have h₁ :=
    Topology.P2_closure_interior_iff_open_closure_interior
      (X := X) (A := A)
  have h₂ :=
    Topology.P3_closure_interior_iff_open_closure_interior
      (X := X) (A := A)
  exact h₁.trans h₂.symm