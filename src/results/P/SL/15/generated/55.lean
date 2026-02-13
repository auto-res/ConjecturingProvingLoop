

theorem P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h₁ := (Topology.P2_closure_iff_P3_closure (X := X) (A := A))
  have h₂ := (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A))
  exact h₁.trans h₂