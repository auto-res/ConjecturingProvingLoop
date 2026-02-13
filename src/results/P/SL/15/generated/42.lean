

theorem P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3Closure
  dsimp [Topology.P3] at hP3Closure ⊢
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  have hx_int : x ∈ interior (closure (closure A)) := hP3Closure hx_closure
  simpa [closure_closure] using hx_int