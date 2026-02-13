

theorem Topology.interior_inter_closure_subset_closure_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∩ closure (B : Set X) ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_intA, hx_clB⟩
  -- We prove that `x` belongs to the closure of `A ∩ B`.
  have : (x : X) ∈ closure (A ∩ B) := by
    -- Use the neighbourhood characterization of the closure.
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Consider the open neighbourhood `U ∩ interior A` of `x`.
    have hV_open : IsOpen (U ∩ interior (A : Set X)) :=
      hU_open.inter isOpen_interior
    have hxV : (x : X) ∈ U ∩ interior (A : Set X) := ⟨hxU, hx_intA⟩
    -- Since `x ∈ closure B`, this set meets `B`.
    have h_nonempty :
        ((U ∩ interior (A : Set X)) ∩ B : Set X).Nonempty := by
      have h_prop := (mem_closure_iff).1 hx_clB
      exact h_prop (U ∩ interior (A : Set X)) hV_open hxV
    -- Extract a witness and show it lies in `U ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hy_intA⟩, hyB⟩⟩
    have hyA : (y : X) ∈ A := interior_subset hy_intA
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this