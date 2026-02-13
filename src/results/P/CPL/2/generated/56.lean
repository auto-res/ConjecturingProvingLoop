

theorem P1_relatively_open {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) (hB : Topology.P1 (X:=X) B) : Topology.P1 (X:=X) (A ∩ B) := by
  classical
  -- Unpack the hypothesis for `B`
  unfold Topology.P1 at hB
  -- Unfold the goal
  unfold Topology.P1
  intro x hx
  -- Split the membership information
  have hxA : x ∈ A := hx.1
  have hxB : x ∈ B := hx.2
  -- From `P1 B`
  have hx_clB : x ∈ closure (interior B) := hB hxB
  -- Auxiliary membership
  have hx_aux : x ∈ (A ∩ closure (interior B) : Set X) := by
    exact ⟨hxA, hx_clB⟩
  -- Key inclusion:  `A ∩ closure (interior B) ⊆ closure (A ∩ interior B)`
  have h_subset :
      (A ∩ closure (interior B) : Set X) ⊆ closure (A ∩ interior B) := by
    intro y hy
    rcases hy with ⟨hyA, hyCl⟩
    -- Show `y ∈ closure (A ∩ interior B)`
    have : y ∈ closure (A ∩ interior B) := by
      refine (mem_closure_iff).2 ?_
      intro V hV_open hyV
      -- `V ∩ A` is an open neighbourhood of `y`
      have hVA_open : IsOpen (V ∩ A) := hV_open.inter hA
      have hyVA : y ∈ V ∩ A := ⟨hyV, hyA⟩
      -- Intersect with `interior B` using `hyCl`
      have h_nonempty : ((V ∩ A) ∩ interior B : Set X).Nonempty :=
        (mem_closure_iff).1 hyCl (V ∩ A) hVA_open hyVA
      -- Rearrange the intersection
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm] using h_nonempty
    exact this
  -- Obtain membership in the intermediate closure
  have hx_cl_aux : x ∈ closure (A ∩ interior B) := h_subset hx_aux
  -- `A ∩ interior B ⊆ interior (A ∩ B)`
  have h_subset2 :
      (A ∩ interior B : Set X) ⊆ interior (A ∩ B) := by
    -- Openness
    have h_open : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    -- Inclusion
    have h_sub : (A ∩ interior B : Set X) ⊆ (A ∩ B) := by
      intro y hy
      exact ⟨hy.1, (interior_subset : interior B ⊆ B) hy.2⟩
    -- Use maximality of the interior
    exact interior_maximal h_sub h_open
  -- Pass to closures
  have h_subset2_cl :
      closure (A ∩ interior B) ⊆ closure (interior (A ∩ B)) :=
    closure_mono h_subset2
  -- Finish
  exact h_subset2_cl hx_cl_aux