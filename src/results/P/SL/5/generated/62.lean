

theorem closure_interior_eq_self_of_closed_and_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    closure (interior A) = A := by
  -- We obtain both inclusions separately and then use `le_antisymm`.
  apply le_antisymm
  · -- `closure (interior A)` is contained in `A` because `A` is closed.
    exact
      Topology.closure_interior_subset_of_closed (X := X) (A := A) hClosed
  · -- The converse inclusion follows from `P2`.
    intro x hxA
    -- `P2` yields that `x` belongs to the interior of `closure (interior A)`.
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
    -- Hence `x` lies in `closure (interior A)`.
    exact interior_subset hx_int