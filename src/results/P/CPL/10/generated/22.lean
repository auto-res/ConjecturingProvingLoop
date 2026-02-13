

theorem P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P3 (closure A)) : Topology.P3 A := by
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  have hx_int : x ∈ interior (closure (closure A)) := h hx_closure
  simpa [closure_closure] using hx_int