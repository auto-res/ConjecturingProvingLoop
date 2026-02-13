

theorem Topology.image_closure_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' closure (A : Set X) ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hx_cl, rfl⟩
  -- We show `f x ∈ closure (f '' A)` using the neighbourhood
  -- characterisation of the closure.
  have : f x ∈ closure (f '' A) := by
    -- `mem_closure_iff` reduces the goal to exhibiting, for every
    -- neighbourhood `V` of `f x`, a point of `f '' A` lying in `V`.
    apply (mem_closure_iff).2
    intro V hV_open hxV
    -- The preimage of `V` under `f` is an open neighbourhood of `x`.
    have hU_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
    have hxU : x ∈ f ⁻¹' V := by
      simpa using hxV
    -- Since `x` belongs to the closure of `A`, this neighbourhood
    -- meets `A` non‐trivially.
    have h_nonempty : ((f ⁻¹' V) ∩ A).Nonempty := by
      -- Apply the defining property of membership in the closure.
      have h_closure := (mem_closure_iff).1 hx_cl
      have h := h_closure (f ⁻¹' V) hU_open hxU
      simpa [Set.inter_comm] using h
    -- Map the witness through `f` to obtain the required point in `V ∩ f '' A`.
    rcases h_nonempty with ⟨z, ⟨hzU, hzA⟩⟩
    -- `f z` lies in `V` by construction …
    have hzV : f z ∈ V := by
      have : z ∈ f ⁻¹' V := hzU
      simpa using this
    -- … and in `f '' A` since `z ∈ A`.
    have hz_image : f z ∈ f '' A := ⟨z, hzA, rfl⟩
    exact ⟨f z, And.intro hzV hz_image⟩
  simpa using this