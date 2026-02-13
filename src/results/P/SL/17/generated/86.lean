

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h₁ : Topology.P2 (closure A) ↔ Topology.P3 (closure A) :=
    Topology.P2_closure_iff_P3_closure (A := A)
  have h₂ : Topology.P3 (closure A) ↔ IsOpen (closure A) :=
    Topology.P3_closure_iff_isOpen_closure (A := A)
  exact h₁.trans h₂