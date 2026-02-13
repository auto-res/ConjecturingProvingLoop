

theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ A \ closure B := by
  intro x hx
  -- A point in the interior of `A \ B` certainly lies in `A \ B`.
  have hx_diff : x ∈ A \ B := interior_subset hx
  have hxA : x ∈ A := hx_diff.1
  -- We show that such a point cannot be in `closure B`.
  have hx_not_clB : x ∉ closure B := by
    intro hx_clB
    -- `interior (A \ B)` is an open neighbourhood of `x` contained in the complement of `B`.
    have h_open : IsOpen (interior (A \ B : Set X)) := isOpen_interior
    -- If `x ∈ closure B`, every open neighbourhood of `x` meets `B`.
    have h_nonempty : ((interior (A \ B : Set X)) ∩ B).Nonempty :=
      (mem_closure_iff.1 hx_clB) (interior (A \ B : Set X)) h_open hx
    rcases h_nonempty with ⟨y, hyInt, hyB⟩
    -- But `interior (A \ B)` is contained in `A \ B`, hence disjoint from `B`.
    have : y ∈ A \ B := interior_subset hyInt
    exact (this.2) hyB
  exact And.intro hxA hx_not_clB