

theorem Topology.P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3Closure
  intro x hxA
  have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure (A : Set X))) := hP3Closure hx_closure
  simpa [closure_closure] using hx_int