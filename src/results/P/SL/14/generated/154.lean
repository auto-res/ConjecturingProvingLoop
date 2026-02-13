

theorem Topology.interior_compl_eq_empty_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → interior (Aᶜ) = (∅ : Set X) := by
  intro hDense
  classical
  -- We prove every point is *not* in `interior (Aᶜ)`.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxInt
  -- Since `A` is dense, the closure of `A` is the whole space, hence `x ∈ closure A`.
  have hx_closure : (x : X) ∈ closure (A : Set X) := by
    have hClosure : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
    simpa [hClosure] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact this)
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  have h_open : IsOpen (interior (Aᶜ)) := isOpen_interior
  -- By density, this neighbourhood must meet `A`.
  have h_inter : ((interior (Aᶜ)) ∩ A).Nonempty :=
    (mem_closure_iff).1 hx_closure (interior (Aᶜ)) h_open hxInt
  -- But `interior (Aᶜ)` is contained in `Aᶜ`, contradicting the intersection with `A`.
  rcases h_inter with ⟨y, hyInt, hyA⟩
  have hyNotA : (y : X) ∈ Aᶜ := interior_subset hyInt
  exact (hyNotA hyA).elim