

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A := A)) : Topology.P1 (A := closure A) := by
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hx_closureA
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact h_closure_subset hx_closureA