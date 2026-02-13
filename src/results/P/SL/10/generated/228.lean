

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- We will verify the neighbourhood criterion for `x` with respect to `A ∩ B`.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- Intersect the given neighbourhood with `interior B`, which is open and contains `x`.
  have hUI_open : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
  have hx_UI : x ∈ U ∩ interior B := ⟨hxU, hxIntB⟩
  -- Since `x ∈ closure A`, this new neighbourhood meets `A`.
  have h_nonempty : ((U ∩ interior B) ∩ A).Nonempty :=
    (mem_closure_iff).1 hxClA (U ∩ interior B) hUI_open hx_UI
  -- Re-package the witness to lie in `U ∩ (A ∩ B)`.
  rcases h_nonempty with ⟨y, ⟨hyU, hyIntB⟩, hyA⟩
  refine ⟨y, ?_⟩
  have hyB : y ∈ B := interior_subset hyIntB
  exact ⟨hyU, ⟨hyA, hyB⟩⟩