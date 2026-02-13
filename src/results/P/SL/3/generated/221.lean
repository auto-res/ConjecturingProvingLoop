

theorem interior_closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) ∩ interior ((Aᶜ) : Set X) = (∅ : Set X) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntCl, hxIntCompl⟩
    have h_mem_closure : (x : X) ∈ closure (A : Set X) :=
      interior_subset hxIntCl
    -- Using `interior (Aᶜ) = (closure A)ᶜ`
    have h_not_mem_closure : (x : X) ∈ (closure (A : Set X))ᶜ := by
      have h_eq :=
        interior_complement_eq_complement_closure (A := A)
      simpa [h_eq] using hxIntCompl
    have hFalse : False := h_not_mem_closure h_mem_closure
    cases hFalse
  · exact Set.empty_subset _