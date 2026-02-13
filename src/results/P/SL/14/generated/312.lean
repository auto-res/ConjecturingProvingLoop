

theorem Topology.closureInterior_union_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A ∪ closure (A : Set X))) =
      closure (interior (closure A)) := by
  -- Since `A ⊆ closure A`, the union `A ∪ closure A` is just `closure A`.
  have h_union : (A ∪ closure (A : Set X) : Set X) = closure A := by
    have h_sub : (A : Set X) ⊆ closure A := subset_closure
    exact (Set.union_eq_right.2 h_sub)
  -- Rewriting with this equality yields the desired result.
  simpa [h_union]