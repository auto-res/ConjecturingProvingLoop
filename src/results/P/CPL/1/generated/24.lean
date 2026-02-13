

theorem P1_iff_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ frontier A ⊆ closure (interior A) := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    -- From `P1` we have equality of the two closures.
    have h_eq : closure (interior A) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    -- Show that the frontier is contained in `closure (interior A)`.
    intro x hx
    -- `hx.1 : x ∈ closure A`.
    have hx_cl : (x : X) ∈ closure A := hx.1
    simpa [h_eq] using hx_cl
  · intro hFront
    -- We prove `P1 A`.
    intro x hxA
    by_cases h_int : x ∈ interior A
    · -- If `x` is interior, the result is immediate.
      exact subset_closure h_int
    · -- Otherwise, `x` lies on the frontier.
      have hx_cl : (x : X) ∈ closure A := subset_closure hxA
      have hx_front : x ∈ frontier A := ⟨hx_cl, h_int⟩
      exact hFront hx_front

theorem P1_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : interior (closure (interior A)) = interior (closure A) := by
  simpa [closure_interior_eq_of_P1 (A := A) h]

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hd : closure A = (⊤ : Set X)) : P1 A := by
  intro x hx
  -- Since `A` is closed and dense, it is the whole space.
  have hA_univ : (A : Set X) = (⊤ : Set X) := by
    calc
      (A : Set X) = closure A := by
        simpa using (hA.closure_eq).symm
      _ = (⊤ : Set X) := by
        simpa using hd
  -- The desired inclusion is now immediate.
  simpa [hA_univ, interior_univ, closure_univ]

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hd : closure A = (⊤ : Set X)) : P2 A := by
  intro x hx
  -- Since `A` is closed and dense, it is the whole space.
  have hA_univ : (A : Set X) = (⊤ : Set X) := by
    calc
      (A : Set X) = closure A := (hA.closure_eq).symm
      _ = (⊤ : Set X) := hd
  -- Rewrite `hx` using this fact.
  have hx_univ : (x : X) ∈ (⊤ : Set X) := by
    simpa [hA_univ] using hx
  -- The required interior set is also the whole space.
  simpa [hA_univ, interior_univ, closure_univ] using hx_univ

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.prod A (Set.prod B C)) := by
  -- First derive `P1` for the product `B × C`.
  have hBC : P1 (Set.prod B C) := P1_prod (A := B) (B := C) hB hC
  -- Then apply `P1_prod` once more to get the desired result.
  exact P1_prod (A := A) (B := Set.prod B C) hA hBC

theorem P3_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P3_univ (X := X))

theorem P2_of_frontier_empty {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A = ∅) : P2 A := by
  classical
  -- Step 1: prove `closure A ⊆ interior A`.
  have h_cl_sub : (closure A : Set X) ⊆ interior A := by
    intro x hx_cl
    by_cases hx_int : x ∈ interior A
    · exact hx_int
    ·
      -- Then `x` lies in the frontier, which is empty.
      have hx_front : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        change x ∈ closure A \ interior A
        exact And.intro hx_cl hx_int
      have : x ∈ (∅ : Set X) := by
        simpa [h] using hx_front
      cases this
  -- Step 2: deduce `A ⊆ interior A`.
  have hA_sub_int : (A : Set X) ⊆ interior A := by
    intro x hxA
    exact h_cl_sub (subset_closure hxA)
  -- Step 3: hence `interior A = A`, so `A` is open.
  have h_int_eq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact hA_sub_int
  have hA_open : IsOpen A := by
    simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
  -- Step 4: apply the open-set lemma to obtain `P2 A`.
  exact P2_of_isOpen (A := A) hA_open

theorem P3_of_frontier_empty {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A = ∅) : P3 A := by
  classical
  intro x hxA
  -- First, show that `closure A ⊆ interior A`.
  have h_cl_sub_int : (closure A : Set X) ⊆ interior A := by
    intro y hy_cl
    by_cases hy_int : y ∈ interior A
    · exact hy_int
    ·
      -- Otherwise, `y` is on the frontier, which is empty.
      have hy_front : y ∈ frontier A := by
        change y ∈ (closure A \ interior A : Set X)
        exact ⟨hy_cl, hy_int⟩
      have : y ∈ (∅ : Set X) := by
        simpa [h] using hy_front
      cases this
  -- Hence `A ⊆ interior A`.
  have hA_sub_int : (A : Set X) ⊆ interior A := fun y hyA =>
    h_cl_sub_int (subset_closure hyA)
  -- Therefore `x ∈ interior A`.
  have hx_intA : x ∈ interior A := hA_sub_int hxA
  -- Finally, `interior A ⊆ interior (closure A)`.
  have h_int_subset : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_int_subset hx_intA