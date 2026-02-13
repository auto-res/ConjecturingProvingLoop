

theorem Topology.P2_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P2 A → IsOpen U → Topology.P2 (A ∩ U) := by
  intro hP2A hUopen
  dsimp [Topology.P2] at *
  intro x hxAU
  rcases hxAU with ⟨hxA, hxU⟩
  -- `x` already lies in the interior of the closure of `interior A`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2A hxA
  -- The open set we'll work with.
  set M : Set X := interior (closure (interior A)) ∩ U with hMdef
  have hOpenM : IsOpen M := by
    simpa [hMdef] using (isOpen_interior).inter hUopen
  have hxM : x ∈ M := by
    simpa [hMdef] using And.intro hxInt hxU
  -- Show that `M` is contained in the closure of `interior (A ∩ U)`.
  have hSubM : (M : Set X) ⊆ closure (interior (A ∩ U)) := by
    intro y hyM
    have hyIntA : y ∈ interior (closure (interior A)) := by
      simpa [hMdef] using hyM.1
    have hyU : y ∈ U := by
      simpa [hMdef] using hyM.2
    -- From `hyIntA` we deduce `y ∈ closure (interior A)`.
    have hyClA : y ∈ closure (interior A) := interior_subset hyIntA
    -- We first show `y ∈ closure (interior A ∩ U)`.
    have hClosure1 : y ∈ closure (interior A ∩ U) := by
      -- Use the neighbourhood characterisation of closure.
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- `V ∩ U` is an open neighbourhood of `y`.
      have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- Since `y ∈ closure (interior A)`, this neighbourhood meets `interior A`.
      have hNonempty : ((V ∩ U) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ U) hVUopen hyVU
      -- Rearrange intersections to fit the goal.
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using hNonempty
    -- `interior A ∩ U` is open and contained in `interior (A ∩ U)`.
    have hIncl : (interior A ∩ U : Set X) ⊆ interior (A ∩ U) := by
      -- Openness.
      have hOpen : IsOpen (interior A ∩ U) := (isOpen_interior).inter hUopen
      -- Containment.
      have hSub : (interior A ∩ U : Set X) ⊆ A ∩ U := by
        intro z hz
        exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
      exact interior_maximal hSub hOpen
    -- Monotonicity of closure turns the previous step into the desired inclusion.
    have hClosureIncl : closure (interior A ∩ U) ⊆ closure (interior (A ∩ U)) :=
      closure_mono hIncl
    exact hClosureIncl hClosure1
  -- Maximality of the interior now yields the result.
  have hFinal :
      (M : Set X) ⊆ interior (closure (interior (A ∩ U))) :=
    interior_maximal hSubM hOpenM
  -- Conclude for our original `x`.
  exact hFinal hxM