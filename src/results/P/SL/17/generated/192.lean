

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) :
    interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We use the characterization `s = ∅ ↔ ∀ x, x ∉ s`.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxInt
  -- Since `A` is dense, every point belongs to `closure A = univ`.
  have hx_closureA : x ∈ closure A := by
    have : x ∈ (Set.univ : Set X) := by simp
    simpa [hDense.closure_eq] using this
  -- The open set `interior (Aᶜ)` contains `x`; by density it meets `A`.
  have h_nonempty :=
    (mem_closure_iff).1 hx_closureA (interior (Aᶜ)) isOpen_interior hxInt
  rcases h_nonempty with ⟨y, hyIntCompl, hyA⟩
  -- But `interior (Aᶜ)` is contained in `Aᶜ`, so `y ∉ A`, contradiction.
  have hyAc : y ∈ Aᶜ := interior_subset hyIntCompl
  exact hyAc hyA