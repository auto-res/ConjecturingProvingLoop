

theorem P3_closure_iff_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure A := by
  have h₁ := (Topology.P3_closure_iff_open_closure (A := A))
  have h₂ := (open_closure_iff_interior_eq_self (A := A))
  exact h₁.trans h₂