

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 (Set.prod (Set.prod A B) C) := by
  intro hA hB hC
  have hAB : P1 (Set.prod A B) := P1_prod (A := A) (B := B) hA hB
  exact P1_prod (A := Set.prod A B) (B := C) hAB hC

theorem P1_of_finset_union {X : Type*} [TopologicalSpace X] {ι : Type*} {s : Finset ι} {A : ι → Set X} : (∀ i, i ∈ s → P1 (A i)) → P1 (⋃ i ∈ s, A i) := by
  classical
  intro hAll
  -- We build the required statement by induction on the finset `s`.
  have hMain :
      (∀ i, i ∈ s → P1 (A i)) → P1 (⋃ i ∈ s, A i) := by
    refine s.induction ?hbase ?hstep
    -- Base case: `s = ∅`
    · intro _hAll
      simpa using (P1_empty : P1 (∅ : Set X))
    -- Induction step: add an element `a`
    · intro a t ha_not_mem ih hAll'
      -- `P1` for the new element `a`
      have hA : P1 (A a) :=
        hAll' a (by
          have : (a : ι) ∈ insert a t := Finset.mem_insert_self a t
          exact this)
      -- `P1` for the old finset `t`
      have hT : P1 (⋃ i ∈ t, A i) := ih (by
        intro i hi_t
        exact hAll' i (Finset.mem_insert_of_mem hi_t))
      -- Combine the two using `P1_union`
      have h_union : P1 ((A a) ∪ ⋃ i ∈ t, A i) := P1_union hA hT
      -- Identify the two unions
      have h_eq :
          (⋃ i ∈ insert a t, A i) = (A a) ∪ ⋃ i ∈ t, A i := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
          rcases Set.mem_iUnion.1 hx with ⟨hi_insert, hxAi⟩
          have hmem : i = a ∨ i ∈ t := (Finset.mem_insert).1 hi_insert
          cases hmem with
          | inl h_eq_i =>
              cases h_eq_i
              exact Or.inl hxAi
          | inr hi_t =>
              have : x ∈ ⋃ i ∈ t, A i := by
                refine Set.mem_iUnion.2 ⟨i, ?_⟩
                refine Set.mem_iUnion.2 ⟨hi_t, hxAi⟩
              exact Or.inr this
        · intro hx
          cases hx with
          | inl hxA =>
              exact
                Set.mem_iUnion.2
                  ⟨a, Set.mem_iUnion.2 ⟨Finset.mem_insert_self a t, hxA⟩⟩
          | inr hx_t =>
              rcases Set.mem_iUnion.1 hx_t with ⟨i, hx_i⟩
              rcases Set.mem_iUnion.1 hx_i with ⟨hi_t, hxAi⟩
              exact
                Set.mem_iUnion.2
                  ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_insert_of_mem hi_t, hxAi⟩⟩
      simpa [h_eq] using h_union
  exact hMain hAll