

theorem Topology.P3_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P3 A → IsOpen U → Topology.P3 (A ∩ U) := by
  intro hP3A hUopen
  dsimp [Topology.P3] at hP3A ⊢
  intro x hxAU
  rcases hxAU with ⟨hxA, hxU⟩
  have hxInt : x ∈ interior (closure A) := hP3A hxA
  -- `S` is an open neighbourhood of `x`
  have hOpenS : IsOpen (interior (closure A) ∩ U) :=
    (isOpen_interior).inter hUopen
  have hSubS : (interior (closure A) ∩ U : Set X) ⊆ closure (A ∩ U) := by
    intro y hy
    have hyInt : y ∈ interior (closure A) := hy.1
    have hyU   : y ∈ U := hy.2
    have hyClA : y ∈ closure A := interior_subset hyInt
    -- Show `y ∈ closure (A ∩ U)`
    have hMem : y ∈ closure (A ∩ U) := by
      -- Employ the neighbourhood characterisation of closure
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Work with the open neighbourhood `V ∩ U` of `y`
      have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- Since `y ∈ closure A`, this neighbourhood meets `A`
      have hNonempty : ((V ∩ U) ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ U) hVUopen hyVU
      -- Re-arrange intersections to obtain the required non-emptiness
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hNonempty
    exact hMem
  have hxS : x ∈ interior (closure A) ∩ U := ⟨hxInt, hxU⟩
  -- Maximality of the interior gives the desired inclusion
  have hIncl : (interior (closure A) ∩ U : Set X) ⊆
      interior (closure (A ∩ U)) :=
    interior_maximal hSubS hOpenS
  exact hIncl hxS