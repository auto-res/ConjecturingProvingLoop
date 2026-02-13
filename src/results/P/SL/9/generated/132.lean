

theorem Topology.closure_union_eq {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure (A ∪ B) = closure A ∪ closure B := by
  apply subset_antisymm
  ·
    -- First, show that `closure (A ∪ B)` is contained in `closure A ∪ closure B`.
    have h_subset : (A ∪ B : Set X) ⊆ closure A ∪ closure B := by
      intro x hx
      cases hx with
      | inl hxA => exact Or.inl (subset_closure hxA)
      | inr hxB => exact Or.inr (subset_closure hxB)
    -- The set on the right is closed, so the minimality of the closure gives the inclusion.
    have h_closed : IsClosed (closure A ∪ closure B) :=
      IsClosed.union isClosed_closure isClosed_closure
    exact closure_minimal h_subset h_closed
  ·
    -- The reverse inclusion is already available.
    exact Topology.closure_union_subset (A) (B)