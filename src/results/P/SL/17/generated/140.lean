

theorem Topology.P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ := Topology.P2_closure_interior_iff_isOpen_closure_interior (A := A)
  have h₂ := Topology.P3_closure_interior_iff_isOpen_closure_interior (A := A)
  exact h₁.trans h₂.symm