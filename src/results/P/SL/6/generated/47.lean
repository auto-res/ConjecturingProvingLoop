

theorem P1_implies_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP1
  -- From `P1`, obtain the equality of closures.
  have hClosure :
      closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Apply `interior` to both sides.
  have hInterior :
      interior (closure (interior A)) = interior (closure A) :=
    congrArg interior hClosure
  -- Rearrange to match the desired orientation.
  simpa using hInterior.symm