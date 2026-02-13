

theorem Topology.P3_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (U ∩ A) := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxUA
  rcases hxUA with ⟨hxU, hxA⟩
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- Define an open neighbourhood of `x` that we will eventually place inside
  -- `closure (U ∩ A)`.
  have hV_open : IsOpen (interior (closure A) ∩ U) :=
    isOpen_interior.inter hU
  have hxV : x ∈ interior (closure A) ∩ U := ⟨hxInt, hxU⟩
  -- Show that this neighbourhood is actually contained in `closure (U ∩ A)`.
  have hV_subset : (interior (closure A) ∩ U) ⊆ closure (U ∩ A) := by
    intro y hy
    have hyInt : y ∈ interior (closure A) := hy.1
    have hyU  : y ∈ U := hy.2
    have hyClA : y ∈ closure A := interior_subset hyInt
    -- Use the neighbourhood characterization of the closure.
    have : y ∈ closure (U ∩ A) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      have hVU_open : IsOpen (V ∩ U) := hVopen.inter hU
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      have h_nonempty : (V ∩ U ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ U) hVU_open hyVU
      simpa [Set.inter_assoc, Set.inter_left_comm] using h_nonempty
    exact this
  -- Conclude that `x` lies in the desired interior.
  exact
    (interior_maximal hV_subset hV_open) hxV