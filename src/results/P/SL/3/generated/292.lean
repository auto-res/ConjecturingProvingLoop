

theorem interior_inter_closure_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ closure (B : Set X) ⊆ closure ((A ∩ B) : Set X) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We show that `x` belongs to the closure of `A ∩ B`
  have h : (x : X) ∈ closure ((A ∩ B) : Set X) := by
    -- Use the neighbourhood characterization of `closure`
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Consider the open neighbourhood `U ∩ interior A` of `x`
    have hVopen : IsOpen (U ∩ interior (A : Set X)) := hUopen.inter isOpen_interior
    have hxV : (x : X) ∈ U ∩ interior (A : Set X) := And.intro hxU hxIntA
    -- Since `x ∈ closure B`, this neighbourhood meets `B`
    have hNonempty :
        ((U ∩ interior (A : Set X)) ∩ (B : Set X)).Nonempty :=
      (mem_closure_iff).1 hxClB _ hVopen hxV
    -- Extract a witness in `A ∩ B` that also lies in `U`
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyIntA⟩, hyB⟩⟩
    have hyA : (y : X) ∈ (A : Set X) := interior_subset hyIntA
    exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩
  exact h