

theorem Topology.P1_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P1 A → IsOpen U → Topology.P1 (A ∩ U) := by
  intro hP1A hUopen
  -- Unfold the goal definition of `P1`.
  dsimp [Topology.P1] at *
  intro x hxAU
  -- Split membership in the intersection.
  rcases hxAU with ⟨hxA, hxU⟩
  -- From `P1 A` we already have membership in `closure (interior A)`.
  have hx_closure_intA : x ∈ closure (interior A) := hP1A hxA
  -- We first prove that `x ∈ closure (interior A ∩ U)`.
  have hx_closure_intA_U : x ∈ closure (interior A ∩ U) := by
    -- Use the neighbourhood characterisation of closures.
    have hClosure := (mem_closure_iff).1 hx_closure_intA
    -- Show that every open neighbourhood `V` of `x` meets `interior A ∩ U`.
    have : ∀ V, IsOpen V → x ∈ V → (V ∩ (interior A ∩ U)).Nonempty := by
      intro V hVopen hxV
      -- Work with `V ∩ U`, still an open neighbourhood of `x`.
      have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
      have hxVU : x ∈ V ∩ U := ⟨hxV, hxU⟩
      -- This neighbourhood meets `interior A` by definition of closure.
      have hNonempty : (V ∩ U ∩ interior A).Nonempty :=
        hClosure _ hVUopen hxVU
      -- Re-arrange intersections.
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using hNonempty
    -- Re-assemble the closure information.
    exact (mem_closure_iff).2 this
  -- Next, relate `interior A ∩ U` to `interior (A ∩ U)`.
  have hSub : (interior A ∩ U : Set X) ⊆ interior (A ∩ U) := by
    -- `interior A ∩ U` is open.
    have hOpen : IsOpen (interior A ∩ U) := (isOpen_interior).inter hUopen
    -- It is contained in `A ∩ U`.
    have hIncl : (interior A ∩ U : Set X) ⊆ A ∩ U := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    -- Use the maximality property of `interior`.
    exact interior_maximal hIncl hOpen
  -- Monotonicity of `closure` finishes the proof.
  exact (closure_mono hSub) hx_closure_intA_U