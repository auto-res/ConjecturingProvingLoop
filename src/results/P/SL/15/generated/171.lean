

theorem P3_and_closure_eq_closure_interior_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior A) → Topology.P2 A := by
  intro hP3 hEq
  have hAnd : Topology.P3 A ∧ closure A = closure (interior A) := ⟨hP3, hEq⟩
  exact
    ((Topology.P2_iff_P3_and_closure_eq_closure_interior
        (X := X) (A := A)).2 hAnd)