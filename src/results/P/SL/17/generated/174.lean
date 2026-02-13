

theorem Topology.P2_inter_isOpen_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- Expand the definition of `P2`.
  unfold Topology.P2 at *
  -- Take an arbitrary point `x` in `A ∩ B`.
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P2` for `B`, obtain the required membership.
  have hxIntB : x ∈ interior (closure (interior B)) := hP2B hxB
  -- Consider the open set `A ∩ interior (closure (interior B))` that contains `x`.
  have hxS : x ∈ A ∩ interior (closure (interior B)) := ⟨hxA, hxIntB⟩
  -- We will show this open set is contained in `closure (interior (A ∩ B))`.
  have h_subset :
      (A ∩ interior (closure (interior B))) ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyA, hyIntB⟩
    -- `y` belongs to the closure of `interior B`.
    have hyClB : y ∈ closure (interior B) := interior_subset hyIntB
    -- Show that `y` lies in the closure of `interior (A ∩ B)`.
    have : y ∈ closure (interior (A ∩ B)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro U hU_open hyU
      -- Refine the neighbourhood to stay inside `A`, which is open.
      have hV_open : IsOpen (U ∩ A) := hU_open.inter hOpenA
      have hyV : y ∈ U ∩ A := ⟨hyU, hyA⟩
      -- Since `y ∈ closure (interior B)`, this refined neighbourhood meets `interior B`.
      have h_nonempty :
          ((U ∩ A) ∩ interior B).Nonempty := by
        have h :=
          (mem_closure_iff).1 hyClB (U ∩ A) hV_open hyV
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hzIntB⟩⟩
      -- Show that `z ∈ interior (A ∩ B)`.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        -- The set `A ∩ interior B` is an open subset of `A ∩ B` containing `z`.
        have h_open : IsOpen (A ∩ interior B) := hOpenA.inter isOpen_interior
        have h_sub : (A ∩ interior B) ⊆ A ∩ B := by
          intro t ht; exact ⟨ht.1, interior_subset ht.2⟩
        have hz_mem : z ∈ A ∩ interior B := ⟨hzA, hzIntB⟩
        have h_incl : (A ∩ interior B) ⊆ interior (A ∩ B) :=
          interior_maximal h_sub h_open
        exact h_incl hz_mem
      -- Conclude that `U` meets `interior (A ∩ B)`.
      exact ⟨z, ⟨hzU, hzIntAB⟩⟩
    exact this
  -- The set we constructed is open.
  have h_openS : IsOpen (A ∩ interior (closure (interior B))) :=
    hOpenA.inter isOpen_interior
  -- Apply `interior_maximal` to obtain the desired inclusion.
  have h_interior :
      (A ∩ interior (closure (interior B))) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal h_subset h_openS
  -- Finish the proof by applying the inclusion to `x`.
  exact h_interior hxS