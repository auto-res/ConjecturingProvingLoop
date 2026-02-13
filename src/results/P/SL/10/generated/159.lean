

theorem Topology.image_closure_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' closure A ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxCl, rfl⟩
  -- We will verify the neighbourhood criterion for `f x`.
  refine (mem_closure_iff).2 ?_
  intro V hVopen hfxV
  -- The preimage of `V` is an open neighbourhood of `x`.
  have hPreOpen : IsOpen (f ⁻¹' V) := hVopen.preimage hf
  have hxPre : x ∈ f ⁻¹' V := hfxV
  -- Since `x ∈ closure A`, this neighbourhood meets `A`.
  have hNonempty : ((f ⁻¹' V) ∩ A).Nonempty :=
    (mem_closure_iff).1 hxCl (f ⁻¹' V) hPreOpen hxPre
  rcases hNonempty with ⟨z, hzPre, hzA⟩
  -- Map the witness forward to obtain a point in `V ∩ f '' A`.
  exact ⟨f z, And.intro hzPre ⟨z, hzA, rfl⟩⟩