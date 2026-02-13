

theorem closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (closure (A : Set X) ∩ interior (B : Set X)) ⊆
      closure (A ∩ B : Set X) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- Prove `x ∈ closure (A ∩ B)` using the neighbourhood criterion.
  have : x ∈ closure (A ∩ B : Set X) := by
    refine (mem_closure_iff).2 ?_
    intro U hU_open hxU
    -- Consider the open neighbourhood `U ∩ interior B` of `x`.
    have hV_open : IsOpen (U ∩ interior (B : Set X)) :=
      hU_open.inter isOpen_interior
    have hxV : x ∈ U ∩ interior (B : Set X) := ⟨hxU, hxIntB⟩
    -- Since `x ∈ closure A`, this neighbourhood intersects `A`.
    have hNonempty : ((U ∩ interior (B : Set X)) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClA (U ∩ interior (B : Set X)) hV_open hxV
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
    -- The point `y` lies in `U ∩ (A ∩ B)`.
    have hy : y ∈ U ∩ (A ∩ B) := by
      have hyB : y ∈ (B : Set X) := interior_subset hyIntB
      exact ⟨hyU, ⟨hyA, hyB⟩⟩
    exact ⟨y, hy⟩
  exact this