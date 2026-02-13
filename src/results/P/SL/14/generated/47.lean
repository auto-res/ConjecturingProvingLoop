

theorem Topology.P3_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hx
  -- Since `x ∈ A`, we have `x ∈ closure A`.
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  -- From `P3 (closure A)`, we know `closure A ⊆ interior (closure (closure A))`.
  have h_subset : (closure A : Set X) ⊆ interior (closure (closure A)) := hP3
  -- Hence `x` lies in `interior (closure (closure A))`.
  have hx_int : (x : X) ∈ interior (closure (closure A)) := h_subset hx_closure
  -- But `closure (closure A)` is just `closure A`.
  simpa [closure_closure] using hx_int