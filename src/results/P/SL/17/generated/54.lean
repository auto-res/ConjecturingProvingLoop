

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  unfold Topology.P1 at *
  intro x hx
  have h_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact h_subset hx