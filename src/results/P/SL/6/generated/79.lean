

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  -- From `P1`, obtain the equality of closures.
  have hClosure :
      closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Unfold the goal.
  dsimp [Topology.P2]
  intro x hxA
  -- Use `P3` to place `x` inside `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- Reinterpret this membership via the equality of interiors.
  have hIntEq :
      interior (closure (interior A)) = interior (closure A) :=
    congrArg interior hClosure
  simpa [hIntEq] using hxInt