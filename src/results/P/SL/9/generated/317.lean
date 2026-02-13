

theorem Topology.isClosed_iff_frontier_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A ↔ frontier (A : Set X) ⊆ A := by
  classical
  constructor
  · intro hClosed
    exact Topology.frontier_subset_of_isClosed (A := A) hClosed
  · intro hSubset
    -- First, show `closure A ⊆ A`.
    have h_closure_subset : closure (A : Set X) ⊆ A := by
      intro x hx_cl
      -- Using `closure A = A ∪ frontier A`.
      have hx_union : x ∈ (A : Set X) ∪ frontier (A : Set X) := by
        simpa [Topology.closure_eq_self_union_frontier (A := A)] using hx_cl
      cases hx_union with
      | inl hA       => exact hA
      | inr hFront   => exact hSubset hFront
    -- Hence `closure A = A`.
    have h_eq : closure (A : Set X) = A :=
      Set.Subset.antisymm h_closure_subset subset_closure
    -- Conclude that `A` is closed.
    have h_closed_closure : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [h_eq] using h_closed_closure