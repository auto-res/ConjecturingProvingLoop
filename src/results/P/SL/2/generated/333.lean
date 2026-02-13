

theorem Topology.closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∩ interior (Aᶜ : Set X) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · -- Show that the intersection is contained in `∅`.
    intro x hx
    rcases hx with ⟨hxCl, hxInt⟩
    -- Use the neighbourhood formulation of `closure`.
    have h :=
      (mem_closure_iff.1 hxCl) (interior (Aᶜ : Set X)) isOpen_interior hxInt
    rcases h with ⟨y, hyInt, hyA⟩
    -- `y` is simultaneously in `A` and `Aᶜ`, contradiction.
    have hyNotA : (y : X) ∉ (A : Set X) := by
      have : (y : X) ∈ (Aᶜ : Set X) := interior_subset hyInt
      simpa [Set.mem_compl] using this
    exact (hyNotA hyA).elim
  · -- The empty set is contained in every set.
    exact Set.empty_subset _