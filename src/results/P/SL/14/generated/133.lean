

theorem Topology.P2_inter_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` lies in `interior (closure (interior A))` by `P2 A`.
  have hxA_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- Auxiliary open set around `x`.
  have h_open_aux :
      IsOpen (B ∩ interior (closure (interior A))) :=
    IsOpen.inter hB_open isOpen_interior
  -- This auxiliary set is contained in `closure (interior (A ∩ B))`.
  have h_subset_aux :
      (B ∩ interior (closure (interior A)) : Set X) ⊆
        closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyB, hyIntA⟩
    -- `y` lies in the closure of `interior A`.
    have hy_closureA : (y : X) ∈ closure (interior A) :=
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A)) hyIntA
    -- Show that every neighbourhood of `y` meets `interior (A ∩ B)`.
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      refine (mem_closure_iff).2 ?_
      intro U hU hyU
      -- `U ∩ B` is an open neighbourhood of `y`.
      have hUB_open : IsOpen (U ∩ B) := IsOpen.inter hU hB_open
      have hyUB : (y : X) ∈ U ∩ B := ⟨hyU, hyB⟩
      -- Since `y ∈ closure (interior A)`, `U ∩ B` meets `interior A`.
      have h_nonempty : ((U ∩ B) ∩ interior A).Nonempty :=
        ((mem_closure_iff).1 hy_closureA) (U ∩ B) hUB_open hyUB
      -- A point in this intersection lies in `interior (A ∩ B)`.
      rcases h_nonempty with ⟨z, ⟨hzU, hzB⟩, hzIntA⟩
      -- `interior A ∩ B` is an open subset of `A ∩ B`, hence contained in its interior.
      have hz_interior : (z : X) ∈ interior (A ∩ B) := by
        have h_open : IsOpen (interior A ∩ B) :=
          IsOpen.inter isOpen_interior hB_open
        have h_subset :
            (interior A ∩ B : Set X) ⊆ A ∩ B := by
          intro w hw; exact ⟨interior_subset hw.1, hw.2⟩
        have h_interior_max :=
          interior_maximal h_subset h_open
        exact h_interior_max ⟨hzIntA, hzB⟩
      -- Finally, `z` witnesses that `U` meets `interior (A ∩ B)`.
      refine ⟨z, hzU, hz_interior⟩
    exact this
  -- The auxiliary open set lies inside the desired interior.
  have h_aux_incl :
      (B ∩ interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal h_subset_aux h_open_aux
  -- Since `x` belongs to the auxiliary open set, it belongs to the target interior.
  have hx_aux : (x : X) ∈ B ∩ interior (closure (interior A)) :=
    ⟨hxB, hxA_int⟩
  exact h_aux_incl hx_aux