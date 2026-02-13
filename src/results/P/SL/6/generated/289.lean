

theorem P2_closure_iff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔
      closure (A : Set X) ⊆ interior (closure A) := by
  have h₁ :=
    (Topology.P3_closure_iff_P2_closure (A := A)).symm
  have h₂ :=
    (Topology.P3_closure_iff_subset_interior_closure (A := A))
  exact h₁.trans h₂