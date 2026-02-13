

theorem Topology.interiorClosure_union_interior_eq_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A ∪ interior A : Set X)) =
      interior (closure (A : Set X)) := by
  -- We apply the more general lemma with `B = interior A`.
  refine
    Topology.interiorClosure_union_eq_interiorClosure
      (A := A) (B := interior A) ?_
  -- Verify the required subset condition.
  intro x hx
  exact
    (Topology.interior_subset_interiorClosure (A := A)) hx