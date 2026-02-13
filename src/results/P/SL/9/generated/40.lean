

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (A := closure A)) : Topology.P3 (A := A) := by
  dsimp [Topology.P3] at h ⊢
  intro x hxA
  have hx_closure : x ∈ closure A := Set.subset_closure hxA
  have hx_int : x ∈ interior (closure (closure A)) := h hx_closure
  simpa [closure_closure] using hx_int