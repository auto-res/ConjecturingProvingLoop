

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- We will use the characterization of the closure via open neighbourhoods.
  refine (mem_closure_iff).2 ?_
  intro U hU hxU
  -- Consider the open set `U ∩ interior B`, which still contains `x`.
  have hU' : IsOpen (U ∩ interior B) := hU.inter isOpen_interior
  have hxU' : x ∈ U ∩ interior B := ⟨hxU, hxB⟩
  -- Since `x ∈ closure A`, this open set intersects `A`.
  have hNon : ((U ∩ interior B) ∩ A).Nonempty :=
    (mem_closure_iff.1 hxA) _ hU' hxU'
  rcases hNon with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
  -- From `y ∈ interior B` we get `y ∈ B`.
  have hyB : y ∈ B := interior_subset hyIntB
  -- Hence `y ∈ U ∩ (A ∩ B)`.
  exact ⟨y, ⟨hyU, hyA, hyB⟩⟩