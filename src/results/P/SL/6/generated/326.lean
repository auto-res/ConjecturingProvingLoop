

theorem interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP2
  -- `P2` yields the equality of the two closures.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Hence their interiors coincide.
  have hIntEq :
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
    simpa using congrArg interior hEq.symm
  -- Use the equality together with `interior_subset`.
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx'