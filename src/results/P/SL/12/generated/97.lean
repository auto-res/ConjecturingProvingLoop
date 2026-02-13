

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure A)) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at h ⊢
  intro x hxA
  -- From `x ∈ A` we know `x ∈ closure A`.
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  -- Apply `P3` for `closure A`.
  have hx_int : x ∈ interior (closure (closure A)) := h hx_cl
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hx_int