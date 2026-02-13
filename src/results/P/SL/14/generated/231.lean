

theorem Topology.interior_inter_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∩ closure (A : Set X)) = interior (A : Set X) := by
  -- Since `A ⊆ closure A`, the intersection `A ∩ closure A` is just `A`.
  have h : (A ∩ closure (A : Set X) : Set X) = A := by
    have hsubset : (A : Set X) ⊆ closure A := subset_closure
    simpa [Set.inter_eq_left.2 hsubset]
  simpa [h]