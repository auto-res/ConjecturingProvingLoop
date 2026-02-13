

theorem Topology.interior_diff_subset_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A \ closure B := by
  intro x hx_int
  -- `x` lies in the interior of `A`
  have hx_intA : x ∈ interior A := by
    have h_sub : (A \ B) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono h_sub) hx_int
  -- `x` is *not* in the closure of `B`
  have hx_not_clB : x ∉ closure B := by
    by_contra h_mem
    -- From `x ∈ closure B`, every open neighbourhood of `x` meets `B`
    -- in particular `interior (A \ B)` (which contains `x`) meets `B`
    have h_nonempty :
        (interior (A \ B) ∩ B).Nonempty := by
      have h_eq := (mem_closure_iff).1 h_mem
      exact h_eq _ isOpen_interior hx_int
    -- Extract a witness `y ∈ interior (A \ B) ∩ B`
    rcases h_nonempty with ⟨y, ⟨hy_int, hy_B⟩⟩
    -- But `interior (A \ B) ⊆ A \ B`, hence `y ∉ B` — contradiction
    have hy_notB : y ∉ B := by
      have : y ∈ A \ B :=
        (interior_subset : interior (A \ B) ⊆ A \ B) hy_int
      exact this.2
    exact hy_notB hy_B
  exact And.intro hx_intA hx_not_clB