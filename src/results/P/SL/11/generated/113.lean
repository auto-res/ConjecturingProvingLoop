

theorem P3_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in `interior (closure A)` by `P3`.
  have hxInt : x ∈ interior (closure A) := hA hxA
  -- Consider the open set `U = interior (closure A) ∩ B` that contains `x`.
  have hxU : x ∈ interior (closure A) ∩ B := ⟨hxInt, hxB⟩
  have hU_open : IsOpen (interior (closure A) ∩ B) :=
    isOpen_interior.inter hB_open
  -- Show that `U ⊆ closure (A ∩ B)`.
  have hU_sub : (interior (closure A) ∩ B : Set X) ⊆ closure (A ∩ B) := by
    intro y hyU
    -- Decompose the membership of `y` in `U`.
    have hyB : y ∈ B := hyU.2
    have hyClA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hyU.1
    -- Use the neighbourhood characterization of closure.
    have : y ∈ closure (A ∩ B) := by
      -- Reformulate via `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro s hs_open hy_in_s
      -- `s ∩ B` is an open neighbourhood of `y`.
      have hOpen' : IsOpen (s ∩ B) := hs_open.inter hB_open
      have hy_in' : y ∈ s ∩ B := ⟨hy_in_s, hyB⟩
      -- Since `y ∈ closure A`, this neighbourhood meets `A`.
      have hNonempty : ((s ∩ B) ∩ A).Nonempty :=
        ((mem_closure_iff).1 hyClA) (s ∩ B) hOpen' hy_in'
      -- Extract a witness in `s ∩ (A ∩ B)`.
      rcases hNonempty with ⟨z, ⟨hz_sB, hzA⟩⟩
      exact ⟨z, ⟨hz_sB.1, ⟨hzA, hz_sB.2⟩⟩⟩
    exact this
  -- `U` is an open neighbourhood of `x` contained in `closure (A ∩ B)`,
  -- hence `x ∈ interior (closure (A ∩ B))`.
  have hxTarget :
      x ∈ interior (closure (A ∩ B)) :=
    (interior_maximal hU_sub hU_open) hxU
  exact hxTarget