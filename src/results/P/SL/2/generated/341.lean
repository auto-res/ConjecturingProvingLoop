

theorem Topology.interior_union_frontier_union_interior_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ frontier (A : Set X) ∪ interior (Aᶜ : Set X) =
      (Set.univ : Set X) := by
  calc
    interior (A : Set X) ∪ frontier (A : Set X) ∪ interior (Aᶜ : Set X)
        = frontier (A : Set X) ∪ (interior (A : Set X) ∪ interior (Aᶜ : Set X)) := by
          -- Reassociate and commute unions so that `frontier A` comes first
          simp [Set.union_left_comm, Set.union_comm, Set.union_assoc]
    _ = frontier (A : Set X) ∪ (frontier (A : Set X))ᶜ := by
          -- Replace the union of interiors with the complement of the frontier
          simpa [Topology.compl_frontier_eq_union_interiors (A := A), Set.union_comm]
    _ = (Set.univ : Set X) := by
          -- A set union its complement is the whole space
          simpa using Set.union_compl_self (frontier (A : Set X))