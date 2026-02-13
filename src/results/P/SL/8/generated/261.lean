

theorem P3_closure_closure_iff_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  have h₁ :=
    (P3_closure_closure_iff (X := X) (A := A))   -- P3 (closure (closure A)) ↔ P3 (closure A)
  have h₂ :=
    (P3_closure_iff_P2_closure (X := X) (A := A)) -- P3 (closure A) ↔ P2 (closure A)
  exact h₁.trans h₂