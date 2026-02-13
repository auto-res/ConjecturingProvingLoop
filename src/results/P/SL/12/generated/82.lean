

theorem Topology.interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  -- From `P2` we know the closures of `A` and `interior A` coincide.
  have hEq : closure (A : Set X) = closure (interior A) :=
    Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hA
  -- Rewrite the source set using this equality.
  have hIntEq :
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
    simpa [hEq]
  -- Establish the desired inclusion.
  intro x hx
  -- Transport membership via the rewritten equality.
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using hx
  -- The interior is always contained in the set it is taken from.
  exact
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) hx'