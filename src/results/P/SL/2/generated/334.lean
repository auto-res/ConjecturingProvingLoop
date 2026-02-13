

theorem Topology.compl_frontier_eq_union_interiors {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (frontier (A : Set X))ᶜ = interior (A : Set X) ∪ interior (Aᶜ : Set X) := by
  calc
    (frontier (A : Set X))ᶜ
        = (closure (A : Set X) ∩ closure (Aᶜ : Set X))ᶜ := by
          simpa [Topology.frontier_eq_closure_inter_closure_compl (A := A)]
    _ = (closure (A : Set X))ᶜ ∪ (closure (Aᶜ : Set X))ᶜ := by
          -- De Morgan’s law for complements
          simp [Set.compl_inter]
    _ = interior (Aᶜ : Set X) ∪ interior (A : Set X) := by
          -- `interior (sᶜ) = (closure s)ᶜ`
          simp [interior_compl]
    _ = interior (A : Set X) ∪ interior (Aᶜ : Set X) := by
          simpa [Set.union_comm]