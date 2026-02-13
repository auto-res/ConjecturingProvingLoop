

theorem Topology.P1_inter_isOpen_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB_open : IsOpen B) : Topology.P1 (A ∩ B) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  have hx_closure_intA : (x : X) ∈ closure (interior A) := hA hxA
  -- We first show `closure (interior A) ∩ B ⊆ closure (interior (A ∩ B))`.
  have h_subset :
      closure (interior A) ∩ B ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hy_closureA, hyB⟩
    -- Use the neighborhood characterization of closure.
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      apply (mem_closure_iff).2
      intro U hU hUy
      -- Consider the open set `U ∩ B`, which contains `y`.
      have hV_open : IsOpen (U ∩ B) := IsOpen.inter hU hB_open
      have hVy : (y : X) ∈ U ∩ B := ⟨hUy, hyB⟩
      -- Since `y ∈ closure (interior A)`, this set meets `interior A`.
      have h_nonempty :
          ((U ∩ B) ∩ interior A).Nonempty :=
        ((mem_closure_iff).1 hy_closureA) (U ∩ B) hV_open hVy
      rcases h_nonempty with ⟨z, hzV, hzIntA⟩
      -- `z` lies in `interior A ∩ B`, which is open and contained in `A ∩ B`.
      have hz_interior_AB : (z : X) ∈ interior (A ∩ B) := by
        have h_open : IsOpen (interior A ∩ B) :=
          IsOpen.inter isOpen_interior hB_open
        have h_sub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
          intro w hw; exact ⟨interior_subset hw.1, hw.2⟩
        have h_max := interior_maximal h_sub h_open
        exact h_max ⟨hzIntA, hzV.2⟩
      have hzU : (z : X) ∈ U := hzV.1
      exact ⟨z, hzU, hz_interior_AB⟩
    exact this
  -- Apply the inclusion to `x`, which belongs to the left-hand side.
  have hx_in : (x : X) ∈ closure (interior A) ∩ B := ⟨hx_closure_intA, hxB⟩
  exact h_subset hx_in