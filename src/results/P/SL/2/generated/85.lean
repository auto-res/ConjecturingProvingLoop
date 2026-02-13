

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)) := by
  have h₁ := (Topology.P2_closure_iff_isOpen_closure (A := A))
  have h₂ := (Topology.P3_closure_iff_isOpen_closure (A := A)).symm
  exact h₁.trans h₂