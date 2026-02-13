

theorem Topology.preimage_closure_subset_closure_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set Y} :
    closure (f ⁻¹' A) ⊆ f ⁻¹' closure A := by
  intro x hx
  -- We show `f x ∈ closure A` using the neighbourhood
  -- characterisation of the closure.
  have h_fx : f x ∈ closure A := by
    -- Apply `mem_closure_iff` at `f x`.
    apply (mem_closure_iff).2
    intro V hV_open h_fxV
    -- Consider the open neighbourhood `f ⁻¹' V` of `x`.
    have hU_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
    have hxU : x ∈ f ⁻¹' V := by
      simpa using h_fxV
    -- Since `x ∈ closure (f ⁻¹' A)`, this neighbourhood meets
    -- `f ⁻¹' A` non‐trivially.
    have h_nonempty : ((f ⁻¹' V) ∩ f ⁻¹' A).Nonempty := by
      have := (mem_closure_iff).1 hx (f ⁻¹' V) hU_open hxU
      simpa [Set.preimage_inter] using this
    -- Map a witnessing point through `f` to obtain a point in `V ∩ A`.
    rcases h_nonempty with ⟨y, hyV, hyA⟩
    have hyV' : f y ∈ V := by
      simpa using hyV
    have hyA' : f y ∈ A := by
      simpa using hyA
    exact ⟨f y, And.intro hyV' hyA'⟩
  -- Reinterpret the membership in terms of the preimage.
  simpa using h_fx