

theorem Topology.closure_inter_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) ∩ interior (closure A) = interior (closure A) := by
  -- `interior (closure A)` is contained in `closure A`.
  have h_subset : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
    interior_subset
  -- Reorder the intersection to apply the lemma, then rewrite back.
  calc
    closure (A : Set X) ∩ interior (closure A)
        = interior (closure A) ∩ closure A := by
          simpa [Set.inter_comm]
    _ = interior (closure A) := by
          exact Set.inter_eq_self_of_subset_left h_subset