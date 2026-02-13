

theorem closureInterior_inter_interiorClosure_subset_closure_inter₂
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ interior (closure B) ⊆ closure (A ∩ closure B) := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxIntClB⟩
  -- We will show `x ∈ closure (A ∩ closure B)` using `mem_closure_iff`.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Set `V = U ∩ interior (closure B)`, an open neighbourhood of `x`.
  let V : Set X := U ∩ interior (closure B)
  have hVopen : IsOpen V := hUopen.inter isOpen_interior
  have hxV : x ∈ V := ⟨hxU, hxIntClB⟩
  -- `x ∈ closure (interior A)` ⇒ `V` meets `interior A`.
  have hNon : (V ∩ interior A).Nonempty := by
    have h := (mem_closure_iff).1 hxClIntA
    simpa [V] using h V hVopen hxV
  -- Extract a witness `y` in `V ∩ interior A`.
  rcases hNon with ⟨y, ⟨⟨hyU, hyIntClB⟩, hyIntA⟩⟩
  -- `y ∈ A` because `y ∈ interior A`.
  have hyA : y ∈ A := interior_subset hyIntA
  -- `y ∈ closure B` because `y ∈ interior (closure B)`.
  have hyClB : y ∈ closure B := interior_subset hyIntClB
  -- Therefore `y ∈ U ∩ (A ∩ closure B)`.
  exact ⟨y, ⟨hyU, ⟨hyA, hyClB⟩⟩⟩