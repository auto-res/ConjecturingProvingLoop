

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior (B : Set X) ⊆ closure (A ∩ B : Set X) := by
  intro x hx
  rcases hx with ⟨h_clA, h_intB⟩
  -- We show that `x` belongs to `closure (A ∩ B)`.
  have : x ∈ closure (A ∩ B : Set X) := by
    -- Use the neighbourhood characterisation of the closure.
    refine (mem_closure_iff.2 ?_)
    intro U hU_open hxU
    -- Consider the open set `U ∩ interior B`, which contains `x`.
    have hV_open : IsOpen (U ∩ interior (B : Set X)) := hU_open.inter isOpen_interior
    have hxV : x ∈ (U ∩ interior (B : Set X)) := And.intro hxU h_intB
    -- Since `x ∈ closure A`, this open set meets `A`.
    have h_nonempty : ((U ∩ interior (B : Set X)) ∩ A).Nonempty := by
      have h_closureA := (mem_closure_iff.1 h_clA)
      exact h_closureA (U ∩ interior (B : Set X)) hV_open hxV
    -- A point in this intersection lies in `U ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hy_intB⟩, hyA⟩⟩
    have hyB : y ∈ (B : Set X) := interior_subset hy_intB
    exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩
  exact this