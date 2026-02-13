

theorem closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxCl, hxInt⟩
    -- We derive a contradiction, showing that the intersection is empty.
    have hContr : False := by
      -- Since `x` is in the closure of `A`, every open neighborhood of `x`
      -- meets `A`. In particular, this holds for `interior (Aᶜ)`.
      have hNonempty :
          ((interior (Aᶜ : Set X)) ∩ (A : Set X)).Nonempty := by
        have h :=
          (mem_closure_iff.1 hxCl) (interior (Aᶜ : Set X)) isOpen_interior hxInt
        -- Reorder the intersection to match the desired form.
        simpa [Set.inter_comm] using h
      rcases hNonempty with ⟨y, ⟨hyIntCompl, hyA⟩⟩
      -- But `y ∈ interior (Aᶜ)` implies `y ∈ Aᶜ`, contradicting `y ∈ A`.
      have : (y : X) ∈ (Aᶜ : Set X) := interior_subset hyIntCompl
      exact (this hyA).elim
    cases hContr
  · exact Set.empty_subset _