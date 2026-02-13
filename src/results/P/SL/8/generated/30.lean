

theorem closure_interior_eq_closure_iff_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = closure A ↔ Topology.P1 A := by
  constructor
  · intro hEq
    dsimp [Topology.P1]
    have h : A ⊆ closure A := subset_closure
    simpa [hEq] using h
  · intro hP1
    exact Topology.P1_imp_closure_interior_eq_closure (X := X) (A := A) hP1