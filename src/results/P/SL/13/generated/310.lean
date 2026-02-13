

theorem Topology.closure_inter_interiorCompl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    have hFalse : False := by
      rcases hx with ⟨h_clA, h_intCompl⟩
      -- Using the neighbourhood characterization of the closure,
      -- obtain a point of `A` inside `interior (Aᶜ)`, which is impossible.
      have h_nonempty :
          ((interior ((A : Set X)ᶜ)) ∩ (A : Set X)).Nonempty := by
        have h := (mem_closure_iff).1 h_clA
        have := h (interior ((A : Set X)ᶜ)) isOpen_interior h_intCompl
        -- Rearrange intersections to the required form.
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using this
      rcases h_nonempty with ⟨y, ⟨hy_intCompl, hyA⟩⟩
      -- The point `y` lies in both `A` and `Aᶜ`, a contradiction.
      have hy_notA : (y : X) ∈ (A : Set X)ᶜ :=
        (interior_subset : interior ((A : Set X)ᶜ) ⊆ (A : Set X)ᶜ) hy_intCompl
      exact hy_notA hyA
    exact hFalse.elim
  · intro hx
    cases hx