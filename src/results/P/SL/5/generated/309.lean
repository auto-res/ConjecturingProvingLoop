

theorem closureInterior_inter_interiorClosure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ interior (closure B) ⊆ closure (A ∩ closure B) := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxIntClB⟩
  -- We prove `x ∈ closure (A ∩ closure B)` via the neighbourhood criterion.
  refine (mem_closure_iff).2 ?_
  intro U hUopen hxU
  -- Consider the open neighbourhood `V = U ∩ interior (closure B)` of `x`.
  let V : Set X := U ∩ interior (closure B)
  have hVopen : IsOpen V := hUopen.inter isOpen_interior
  have hxV : x ∈ V := ⟨hxU, hxIntClB⟩
  -- Since `x ∈ closure (interior A)`, the neighbourhood `V` meets `interior A`.
  have hNon : (V ∩ interior A).Nonempty := by
    have h := (mem_closure_iff).1 hxClIntA
    simpa [V] using h V hVopen hxV
  -- Extract a witness `y`.
  rcases hNon with ⟨y, ⟨⟨hyU, _hyIntClB⟩, hyIntA⟩⟩
  -- `y ∈ A` and `y ∈ closure B`.
  have hyA : y ∈ A := interior_subset hyIntA
  have hyClB : y ∈ closure B := interior_subset _hyIntClB
  -- `y` lies in `U ∩ (A ∩ closure B)`, hence the required non‐emptiness.
  exact ⟨y, ⟨hyU, ⟨hyA, hyClB⟩⟩⟩