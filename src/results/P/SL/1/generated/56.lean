

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2
  -- Obtain `P3` for `closure A` from `P2`.
  have hP3_closure : Topology.P3 (closure A) :=
    P2_implies_P3 (A := closure A) hP2
  -- Unfold definitions to work with subset relations.
  dsimp [Topology.P3] at hP3_closure ⊢
  intro x hx
  -- Since `A ⊆ closure A`, upgrade `x` to a point of `closure A`.
  have hx_closure : x ∈ closure A := subset_closure hx
  -- Apply `P3` for `closure A`.
  have : x ∈ interior (closure (closure A)) := hP3_closure hx_closure
  -- Simplify `closure (closure A)` to conclude.
  simpa [closure_closure] using this