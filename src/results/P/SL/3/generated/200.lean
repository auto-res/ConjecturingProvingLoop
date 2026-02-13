

theorem interior_inter_closure_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ closure (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxInt, hxCl⟩
    have hContr : False := by
      -- From `x ∈ closure (Aᶜ)` we obtain that every open neighbourhood of `x`
      -- meets `Aᶜ`. In particular, this holds for `interior A`, which is an
      -- open neighbourhood of `x`.
      have hNonempty :
          ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
        (mem_closure_iff.1 hxCl) (interior (A : Set X)) isOpen_interior hxInt
      rcases hNonempty with ⟨y, ⟨hyInt, hyCompl⟩⟩
      -- But `y ∈ interior A` implies `y ∈ A`, contradicting `y ∈ Aᶜ`.
      have hInA : (y : X) ∈ (A : Set X) := interior_subset hyInt
      exact (hyCompl hInA)
    cases hContr
  · exact Set.empty_subset _