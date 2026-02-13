

theorem P3_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3Closure
  dsimp [Topology.P3] at hP3Closure
  dsimp [Topology.P3]
  intro x hxA
  -- A point of `A` is in `closure A`.
  have hx_closure : x ∈ closure A := subset_closure hxA
  -- Apply `P3` for `closure A`.
  have hx_int : x ∈ interior (closure (closure A)) := hP3Closure hx_closure
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hx_int