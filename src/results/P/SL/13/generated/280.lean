

theorem Topology.closure_eq_closureInterior_and_P3_implies_P2 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = closure (interior A) →
      Topology.P3 (X:=X) A → Topology.P2 (X:=X) A := by
  intro h_eq hP3
  have h_pair :
      closure (A : Set X) = closure (interior A) ∧ Topology.P3 (X:=X) A :=
    ⟨h_eq, hP3⟩
  exact
    (Topology.P2_iff_closure_eq_closureInterior_and_P3 (X := X) (A := A)).2 h_pair