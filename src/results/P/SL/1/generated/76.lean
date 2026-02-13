

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  have : x ∈ interior (closure (closure A)) := hP3 hx_closure
  simpa [closure_closure] using this