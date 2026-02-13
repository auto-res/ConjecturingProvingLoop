

theorem closure_inter_interior_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ∩ interior (B : Set X) ⊆ closure ((A ∩ B) : Set X) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- We verify the defining property of being in the closure of `A ∩ B`.
  have hxClAB : (x : X) ∈ closure ((A ∩ B) : Set X) := by
    -- Use the neighborhood characterization of closure.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighborhood `U ∩ interior B` of `x`.
    have hOpen' : IsOpen (U ∩ interior (B : Set X)) := hUopen.inter isOpen_interior
    have hxU' : (x : X) ∈ U ∩ interior (B : Set X) := by
      exact And.intro hxU hxIntB
    -- Since `x ∈ closure A`, this neighborhood meets `A`.
    have hNonempty :
        ((U ∩ interior (B : Set X)) ∩ (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hxClA _ hOpen' hxU'
    -- Extract a point witnessing the non‐emptiness and show it lies in
    -- `U ∩ (A ∩ B)`.
    rcases hNonempty with ⟨y, ⟨hyU, hyIntB⟩, hyA⟩
    have hyB : (y : X) ∈ (B : Set X) := interior_subset hyIntB
    exact ⟨y, ⟨hyU, And.intro hyA hyB⟩⟩
  exact hxClAB