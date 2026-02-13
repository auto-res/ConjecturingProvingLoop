

theorem P2_inter_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2] at hP2A ⊢
  intro x hxAB
  -- Split the hypothesis `x ∈ A ∩ B`.
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P2 A`, obtain that `x` is in the relevant interior.
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- We shall work with the open neighbourhood `W := interior (closure (interior A)) ∩ B`.
  let W : Set X := interior (closure (interior A)) ∩ B
  have hW_open : IsOpen W :=
    (isOpen_interior.inter hOpenB)
  have hxW : x ∈ W := ⟨hxIntA, hxB⟩
  -- We next show that every point of `W` lies in `closure (interior (A ∩ B))`.
  have hW_subset :
      (W : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyW
    rcases hyW with ⟨hyIntA, hyB⟩
    -- `y` is in the closure of `interior A`.
    have hyClA : y ∈ closure (interior A) :=
      (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hyIntA
    -- Characterize membership in a closure via neighbourhoods.
    have hMem : y ∈ closure (interior (A ∩ B)) := by
      -- Use the neighbourhood formulation of `closure`.
      refine (mem_closure_iff).2 ?_
      intro U hU_open hyU
      -- Intersect the neighbourhood with `B`, which is open and contains `y`.
      have hV_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
      have hyV : y ∈ U ∩ B := ⟨hyU, hyB⟩
      -- From `hyClA`, the intersection with `interior A` is nonempty.
      have hNonempty :
          ((U ∩ B) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hV_open hyV
      -- Relate `interior (A ∩ B)` to `interior A ∩ B`.
      have hInt_eq :
          interior (A ∩ B : Set X) = interior A ∩ interior B := by
        simpa using interior_inter
      -- Since `B` is open, `interior B = B`.
      have hIntB : interior B = (B : Set X) := hOpenB.interior_eq
      -- The non‐empty intersection yields a point in `U ∩ interior (A ∩ B)`.
      rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzIntA⟩⟩
      have hzIntAB : z ∈ interior (A ∩ B) := by
        have : z ∈ interior A ∩ interior B := by
          have hzIntB : z ∈ interior B := by
            simpa [hIntB] using hzB
          exact ⟨hzIntA, hzIntB⟩
        simpa [hInt_eq] using this
      exact ⟨z, ⟨hzU, hzIntAB⟩⟩
    exact hMem
  -- By maximality of the interior, `W` lies inside `interior (closure (interior (A ∩ B)))`.
  have hW_in :
      (W : Set X) ⊆ interior (closure (interior (A ∩ B))) :=
    interior_maximal hW_subset hW_open
  -- Apply the inclusion to the point `x`.
  exact hW_in hxW