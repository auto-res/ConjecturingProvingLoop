

theorem P1_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB_open : IsOpen B) :
    Topology.P1 (A ∩ B) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in the closure of `interior A`.
  have hx_clA : x ∈ closure (interior A) := hA hxA
  -- We show `x ∈ closure (interior (A ∩ B))`.
  have hx_cl : x ∈ closure (interior (A ∩ B)) := by
    -- Use the neighbourhood characterisation of closures.
    apply (mem_closure_iff).2
    intro s hs_open hxs
    -- `s ∩ B` is an open neighbourhood of `x`.
    have h_open' : IsOpen (s ∩ B) := hs_open.inter hB_open
    have hx_in' : x ∈ s ∩ B := ⟨hxs, hxB⟩
    -- Since `x ∈ closure (interior A)`, this neighbourhood meets `interior A`.
    have h_nonempty : ((s ∩ B) ∩ interior A).Nonempty :=
      ((mem_closure_iff).1 hx_clA) (s ∩ B) h_open' hx_in'
    -- Extract a witness `y`.
    rcases h_nonempty with ⟨y, ⟨hy_sB, hy_intA⟩⟩
    have hy_s : y ∈ s := hy_sB.1
    have hy_B : y ∈ B := hy_sB.2
    -- `y` lies in `interior A` and in `B`.
    -- Show that `y ∈ interior (A ∩ B)`.
    have hy_intAB : y ∈ interior (A ∩ B) := by
      -- `interior A ∩ B` is an open subset of `A ∩ B` containing `y`.
      have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
        intro z hz
        exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
      have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hB_open
      have hSubInt : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
        interior_maximal hSub hOpen
      exact hSubInt ⟨hy_intA, hy_B⟩
    -- Provide the witness in `s ∩ interior (A ∩ B)`.
    exact ⟨y, ⟨hy_s, hy_intAB⟩⟩
  exact hx_cl