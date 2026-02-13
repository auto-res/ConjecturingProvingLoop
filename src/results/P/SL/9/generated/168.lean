

theorem Topology.interior_closureDiffSelf_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X) \ A) = (∅ : Set X) := by
  classical
  -- We prove that `interior (closure A \ A)` contains no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  -- `x` lies in the interior, hence in the set itself.
  have hx_diff : x ∈ closure A \ A :=
    (interior_subset : interior (closure A \ A) ⊆ closure A \ A) hx
  -- In particular, `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx_diff.1
  -- Consider the open neighbourhood `U = interior (closure A \ A)` of `x`.
  have h_open : IsOpen (interior (closure A \ A)) := isOpen_interior
  have h_nonempty :
      ((interior (closure A \ A)) ∩ A).Nonempty :=
    (mem_closure_iff).1 hx_closure _ h_open hx
  -- Extract a point `y ∈ A` that is also in `interior (closure A \ A)`.
  rcases h_nonempty with ⟨y, hyU, hyA⟩
  -- But `interior (closure A \ A)` is contained in `closure A \ A`,
  -- so `y ∉ A`, contradicting `hyA`.
  have hy_notA : y ∉ A := by
    have : y ∈ closure A \ A :=
      (interior_subset : interior (closure A \ A) ⊆ closure A \ A) hyU
    exact this.2
  exact hy_notA hyA