

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  -- Obtain `P1` and `P3` for `A`
  have hP1A : Topology.P1 A := P2_implies_P1 (A := A) hA
  have hP3A : Topology.P3 A := P2_implies_P3 (A := A) hA
  -- `P3` is stable under removing a closed subset
  have hP3Diff : Topology.P3 (A \ B) :=
    P3_diff_closed (A := A) (B := B) hP3A hB
  ------------------------------------------------------------------
  -- We now prove `P1` for the difference `A \ B`.
  ------------------------------------------------------------------
  have hP1Diff : Topology.P1 (A \ B) := by
    -- Unfold the definition
    dsimp [Topology.P1] at hP1A ⊢
    intro x hxDiff
    -- Split the membership information
    have hxA    : x ∈ A   := hxDiff.1
    have hxNotB : x ∉ B   := hxDiff.2
    -- From `P1 A` we know that `x ∈ closure (interior A)`.
    have hx_clA : x ∈ closure (interior A) := hP1A hxA
    -- We show that `x ∈ closure (interior (A \ B))`.
    have hx_clDiff : x ∈ closure (interior (A \ B)) := by
      -- Neighbourhood characterisation of the closure
      apply (mem_closure_iff).2
      intro V hVopen hxV
      -- Refine the neighbourhood so that it avoids `B`
      have hV'open : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
      have hxV'    : x ∈ V ∩ Bᶜ     := ⟨hxV, hxNotB⟩
      -- Since `x ∈ closure (interior A)`, this refined neighbourhood
      -- meets `interior A`.
      have h_nonempty :
          ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
        have hProp := (mem_closure_iff).1 hx_clA
        simpa using hProp (V ∩ Bᶜ) hV'open hxV'
      -- The open set `interior A ∩ Bᶜ` is contained in `interior (A \ B)`.
      have h_subset :
          ((V ∩ Bᶜ) ∩ interior A) ⊆ V ∩ interior (A \ B) := by
        intro y hy
        rcases hy with ⟨⟨hyV, hyNotB⟩, hyIntA⟩
        -- Show that `y ∈ interior (A \ B)`
        have hy_intDiff : y ∈ interior (A \ B) := by
          -- `interior A ∩ Bᶜ` is open and contained in `A \ B`
          have h_open : IsOpen (interior A ∩ Bᶜ) :=
            (isOpen_interior : IsOpen (interior A)).inter hB.isOpen_compl
          have h_sub :
              (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
            intro z hz
            rcases hz with ⟨hzIntA, hzNotB⟩
            exact ⟨interior_subset hzIntA, hzNotB⟩
          exact
            (interior_maximal h_sub h_open) ⟨hyIntA, hyNotB⟩
        exact ⟨hyV, hy_intDiff⟩
      -- Hence `V ∩ interior (A \ B)` is non–empty
      have : (V ∩ interior (A \ B)).Nonempty :=
        h_nonempty.mono h_subset
      exact this
    -- Conclude the required inclusion
    exact hx_clDiff
  -- Combine `P1` and `P3` via the characterisation of `P2`
  simpa using
    (P2_iff_P1_and_P3 (A := A \ B)).2 ⟨hP1Diff, hP3Diff⟩