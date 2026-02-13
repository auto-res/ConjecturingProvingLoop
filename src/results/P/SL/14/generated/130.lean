

theorem Topology.P3_inter_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  have hxA_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Define an auxiliary open set around `x`.
  have h_open_aux : IsOpen (B ∩ interior (closure A)) :=
    IsOpen.inter hB_open isOpen_interior
  -- This open set is contained in `closure (A ∩ B)`.
  have h_subset_aux :
      (B ∩ interior (closure A) : Set X) ⊆ closure (A ∩ B) := by
    intro y hy
    rcases hy with ⟨hyB, hyIntA⟩
    -- `y` lies in `B` and in `interior (closure A)`, hence in `closure A`.
    have hy_closureA : (y : X) ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hyIntA
    -- Show that every neighbourhood of `y` meets `A ∩ B`.
    have : (y : X) ∈ closure (A ∩ B) := by
      refine (mem_closure_iff).2 ?_
      intro U hU hyU
      -- `U ∩ B` is an open neighbourhood of `y`.
      have hUB_open : IsOpen (U ∩ B) := IsOpen.inter hU hB_open
      have hyUB : (y : X) ∈ U ∩ B := And.intro hyU hyB
      -- Since `y ∈ closure A`, `U ∩ B` meets `A`.
      have h_nonempty : ((U ∩ B) ∩ A).Nonempty :=
        (mem_closure_iff).1 hy_closureA (U ∩ B) hUB_open hyUB
      -- Rewriting gives a point in `U ∩ (A ∩ B)`.
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h_nonempty
    exact this
  -- The auxiliary open set lies inside the interior of the target closure.
  have h_aux_incl :
      (B ∩ interior (closure A) : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal h_subset_aux h_open_aux
  -- Since `x` belongs to this auxiliary open set, it belongs to the target interior.
  have hx_aux : (x : X) ∈ B ∩ interior (closure A) :=
    And.intro hxB hxA_int
  exact h_aux_incl hx_aux