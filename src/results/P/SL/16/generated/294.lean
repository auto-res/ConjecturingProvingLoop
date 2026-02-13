

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove that `interior (Aᶜ)` contains no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxInt
  -- Since `closure A = univ`, every point is in `closure A`.
  have hxCl : (x : X) ∈ closure A := by
    simpa [h_dense] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by simp
      exact this)
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  have hOpen : IsOpen (interior (Aᶜ)) := isOpen_interior
  -- By density, this neighbourhood meets `A`.
  have hNonempty : ((interior (Aᶜ) : Set X) ∩ A).Nonempty :=
    (mem_closure_iff.1 hxCl) (interior (Aᶜ)) hOpen hxInt
  rcases hNonempty with ⟨y, hyInt, hyA⟩
  -- But `interior (Aᶜ)` is contained in `Aᶜ`, so `y ∉ A`, contradiction.
  have hNotA : (y : X) ∈ (Aᶜ : Set X) := interior_subset hyInt
  exact hNotA hyA