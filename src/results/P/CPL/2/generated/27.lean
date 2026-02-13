

theorem P1_inter_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (A ∩ closure A) := by
  -- Unpack the definition of `P1`
  unfold Topology.P1 at h ⊢
  -- Since `A ⊆ closure A`, we have `A ∩ closure A = A`
  have h_eq : (A ∩ closure A : Set X) = A := by
    simpa using
      (Set.inter_eq_left.2 (subset_closure : (A : Set X) ⊆ closure A))
  -- Rewriting with this equality reduces the goal to the hypothesis
  simpa [h_eq] using h

theorem exists_closed_P2_of_compact {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ A : Set X, IsClosed A ∧ Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_⟩
  simpa using (Topology.P2_univ (X := X))

theorem closure_eq_inter_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 (X:=X) A) : closure A = closure (interior (closure A)) := by
  have hP3 : P3 A := P3_of_P2 (A := A) hA
  simpa using closure_eq_of_P3 (A := A) hP3

theorem P3_closed_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hd : Dense (interior A)) (hc : IsClosed A) : Topology.P3 (X:=X) A := by
  -- Step 1: show that `A = univ`
  have hA_eq_univ : (A : Set X) = Set.univ := by
    -- `closure (interior A)` is `univ` by density
    have h_cl_int_eq_univ : closure (interior A) = (Set.univ : Set X) :=
      hd.closure_eq
    -- since `A` is closed we have `closure (interior A) ⊆ A`
    have h_subset : closure (interior A) ⊆ (A : Set X) := by
      have : closure (interior A) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hc.closure_eq] using this
    -- hence `univ ⊆ A`
    have h_univ_subset : (Set.univ : Set X) ⊆ (A : Set X) := by
      simpa [h_cl_int_eq_univ] using h_subset
    -- conclude equality
    exact Set.Subset.antisymm (Set.subset_univ _) h_univ_subset
  -- Step 2: rewrite and conclude `P3 A`
  unfold Topology.P3
  simpa [hA_eq_univ, hc.closure_eq, interior_univ]