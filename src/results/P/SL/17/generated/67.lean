

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  unfold Topology.P3 at *
  intro x hxA
  have hx_closure : x ∈ closure A := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure A)) := hP3 hx_closure
  simpa [closure_closure] using hx_int