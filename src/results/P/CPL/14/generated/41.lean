

theorem P1_of_nowhereDense {X} [TopologicalSpace X] {A : Set X} (hN : IsNowhereDense A) : P1 A → A = ∅ := by
  intro hP1
  -- From `IsNowhereDense`, the interior of the closure of `A` is empty.
  have hIntClosure : interior (closure (A : Set X)) = (∅ : Set X) := by
    simpa [IsNowhereDense] using hN
  -- Hence the interior of `A` itself is empty.
  have hIntA : (interior A : Set X) = ∅ := by
    apply Set.Subset.antisymm
    · intro x hx
      have : x ∈ interior (closure A) := by
        have hsubset : (interior A : Set X) ⊆ interior (closure A) :=
          interior_mono (subset_closure : (A : Set X) ⊆ closure A)
        exact hsubset hx
      simpa [hIntClosure] using this
    · exact Set.empty_subset _
  -- Consequently, the closure of the interior of `A` is empty.
  have hClosureInt : closure (interior A) = (∅ : Set X) := by
    simpa [hIntA, closure_empty]
  -- Using `P1`, every point of `A` lies in this empty set, hence `A` is empty.
  have hA_subset_empty : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ closure (interior A) := hP1 hxA
    simpa [hClosureInt] using this
  exact Set.Subset.antisymm hA_subset_empty (Set.empty_subset _)

theorem P3_Union_closure {X} [TopologicalSpace X] {I : Type*} {F : I → Set X} (h : ∀ i, P3 (closure (F i))) : P3 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hP3_cl : P3 (closure (F i)) := h i
  have hx_int : x ∈ interior (closure (F i)) := by
    have h' := hP3_cl (subset_closure hxFi)
    simpa [closure_closure] using h'
  have hsubset :
      (interior (closure (F i)) : Set X) ⊆ interior (closure (⋃ i, F i)) := by
    have hcl_subset : (closure (F i) : Set X) ⊆ closure (⋃ i, F i) := by
      have : (F i : Set X) ⊆ ⋃ i, F i := Set.subset_iUnion _ _
      exact closure_mono this
    exact interior_mono hcl_subset
  exact hsubset hx_int

theorem P3_of_separated {X} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U V, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ Aᶜ ⊆ V ∧ Disjoint U V) : P3 A := by
  -- Use the open–neighbourhood characterisation of `P3`.
  refine (P3_iff_forall_point).2 ?_
  intro x hxA
  -- Obtain separating open sets for the point `x`.
  rcases h x hxA with
    ⟨U, V, hUopen, _hVopen, hxU, hAc_sub_V, hDisj⟩
  -- Show that `U ⊆ closure A`.
  have hU_subset_closure : (U : Set X) ⊆ closure (A : Set X) := by
    intro y hyU
    -- First, prove that `y ∈ A`.
    have h_yA : y ∈ (A : Set X) := by
      classical
      by_cases hA : y ∈ A
      · exact hA
      · -- Otherwise, `y ∈ Aᶜ ⊆ V`, contradicting the disjointness of `U` and `V`.
        have hyV : y ∈ V := hAc_sub_V (by
          simpa using hA)
        have hFalse : False := (Set.disjoint_left.1 hDisj) hyU hyV
        exact (False.elim hFalse)
    -- Hence `y` lies in `closure A`.
    exact subset_closure h_yA
  -- Supply the required neighbourhood data for `P3`.
  exact ⟨U, hUopen, hxU, hU_subset_closure⟩

theorem P2_closed_iff_open_compl {X} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    -- First, we show `A ⊆ interior A`.
    have h_subset_cl : (closure (interior A) : Set X) ⊆ A := by
      have h' : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hA.closure_eq] using h'
    have h_int_subset : interior (closure (interior A)) ⊆ interior A :=
      interior_mono h_subset_cl
    have hA_subset_int : (A : Set X) ⊆ interior A := by
      intro x hxA
      have hx_int_cl : x ∈ interior (closure (interior A)) := hP2 hxA
      exact h_int_subset hx_int_cl
    -- Hence `interior A = A`, so `A` is open.
    have h_eq : (interior A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hA_subset_int
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hOpen
    exact P2_of_open (A := A) hOpen