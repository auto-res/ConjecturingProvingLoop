

theorem P3_closure_interior_iff_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) ↔
      Topology.P2 (closure (interior A)) := by
  have h₁ :=
    (Topology.P3_closure_interior_iff_open_closure_interior
      (A := A))
  have h₂ :=
    (Topology.P2_closure_interior_iff_open_closure_interior
      (A := A))
  simpa using h₁.trans h₂.symm