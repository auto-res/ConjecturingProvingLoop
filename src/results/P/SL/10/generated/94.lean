

theorem Topology.P2_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (U ∩ A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hxUA
  rcases hxUA with ⟨hxU, hxA⟩
  -- `P2 A` supplies a neighbourhood of `x` inside `closure (interior A)`.
  have hx_intA : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Consider the open neighbourhood `V := interior (closure (interior A)) ∩ U` of `x`.
  set V : Set X := interior (closure (interior A)) ∩ U with hVdef
  have hV_open : IsOpen V := (isOpen_interior).inter hU
  have hxV : x ∈ V := by
    have : x ∈ interior (closure (interior A)) ∧ x ∈ U := ⟨hx_intA, hxU⟩
    simpa [hVdef] using this
  -- We show that every point of `V` lies in `closure (interior (U ∩ A))`.
  have hV_subset : V ⊆ closure (interior (U ∩ A)) := by
    intro y hyV
    have hy_intA : y ∈ interior (closure (interior A)) := by
      have : y ∈ V := hyV
      have : y ∈ interior (closure (interior A)) ∧ y ∈ U := by
        simpa [hVdef] using this
      exact this.1
    have hyU : y ∈ U := by
      have : y ∈ V := hyV
      have : y ∈ interior (closure (interior A)) ∧ y ∈ U := by
        simpa [hVdef] using this
      exact this.2
    -- Convert membership in the interior of the closure to the closure itself.
    have hy_closure_intA : y ∈ closure (interior A) :=
      interior_subset hy_intA
    -- Use the neighbourhood characterisation of the closure to prove
    -- `y ∈ closure (interior (U ∩ A))`.
    have : y ∈ closure (interior (U ∩ A)) := by
      -- Reformulate via `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro W hWopen hyW
      -- Intersect the neighbourhood with `U`, which is open and contains `y`.
      have hWU_open : IsOpen (W ∩ U) := hWopen.inter hU
      have hyWU : y ∈ W ∩ U := ⟨hyW, hyU⟩
      -- Since `y ∈ closure (interior A)`, this neighbourhood meets `interior A`.
      have h_nonempty : (W ∩ U ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hy_closure_intA (W ∩ U) hWU_open hyWU
      -- `U` is open, so `U ∩ interior A` sits inside `interior (U ∩ A)`.
      have h_subset : U ∩ interior A ⊆ interior (U ∩ A) := by
        have h_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
        have h_sub : U ∩ interior A ⊆ U ∩ A := by
          intro z hz
          exact ⟨hz.1, interior_subset hz.2⟩
        exact interior_maximal h_sub h_open
      -- Hence the neighbourhood meets `interior (U ∩ A)`.
      have : (W ∩ interior (U ∩ A)).Nonempty := by
        rcases h_nonempty with ⟨z, ⟨hzW, hzU⟩, hzIntA⟩
        have hzIntUA : z ∈ interior (U ∩ A) := h_subset ⟨hzU, hzIntA⟩
        exact ⟨z, ⟨hzW, hzIntUA⟩⟩
      exact this
    exact this
  -- `V` is an open neighbourhood of `x` contained in the target set,
  -- hence `x` is in the interior.
  have : x ∈ interior (closure (interior (U ∩ A))) :=
    (interior_maximal hV_subset hV_open) hxV
  exact this