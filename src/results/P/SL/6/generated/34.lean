

theorem P2_implies_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP2
  -- From P2 we know the closures coincide.
  have hClosure :
      closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Apply `interior` to both sides of the equality.
  have hInterior :
      interior (closure (interior A)) = interior (closure A) :=
    congrArg interior hClosure
  -- Rearrange to the desired orientation.
  simpa using hInterior.symm