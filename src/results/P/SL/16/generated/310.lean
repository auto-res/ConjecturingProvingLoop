

theorem Topology.interior_closure_diff_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior ((closure A) \ A : Set X) = (∅ : Set X) := by
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxInt
  have hxDiff : (x : X) ∈ (closure A \ A : Set X) := by
    exact interior_subset hxInt
  have hxCl : x ∈ closure A := hxDiff.1
  -- Consider the open neighbourhood `interior (closure A \ A)` of `x`.
  have h_open :
      IsOpen (interior ((closure A) \ A : Set X)) := isOpen_interior
  -- By density of `A` in its closure, this neighbourhood meets `A`.
  have h_nonempty :
      ((interior ((closure A) \ A : Set X)) ∩ A : Set X).Nonempty :=
    (mem_closure_iff.1 hxCl) _ h_open hxInt
  rcases h_nonempty with ⟨y, ⟨hyInt, hyA⟩⟩
  -- But each point of `interior (closure A \ A)` lies outside `A`.
  have h_subset :
      (interior ((closure A) \ A : Set X) : Set X) ⊆ (closure A \ A) :=
    interior_subset
  have hyNotA : (y : X) ∉ A := (h_subset hyInt).2
  exact hyNotA hyA