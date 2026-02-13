

theorem P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure (A : Set X))) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at *
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure (A : Set X))) := h hx_cl
  simpa [closure_closure] using hx_int