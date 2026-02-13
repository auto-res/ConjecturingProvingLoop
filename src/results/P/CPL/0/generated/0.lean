

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact fun x hx =>
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (hP2 hx)

theorem exists_subset_P2 {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P2 B := by
  refine ⟨(∅ : Set X), ?_, ?_⟩
  · intro x hx
    cases hx
  · intro x hx
    cases hx

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_clA : x ∈ closure (interior A : Set X) := hA hxA
      have h_sub : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : interior A ⊆ interior (A ∪ B) := by
          have h_set : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_set
        exact closure_mono h_int
      exact h_sub hx_clA
  | inr hxB =>
      have hx_clB : x ∈ closure (interior B : Set X) := hB hxB
      have h_sub : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : interior B ⊆ interior (A ∪ B) := by
          have h_set : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_set
        exact closure_mono h_int
      exact h_sub hx_clB

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ interior (closure (interior A))`
      have hx_intA : x ∈ interior (closure (interior (A : Set X))) := hA hxA
      -- show this set is contained in the required one
      have h_subset :
          interior (closure (interior (A : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) := by
        -- step 1: `interior A ⊆ interior (A ∪ B)`
        have h_int_sub : interior (A : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        -- step 2: take closures
        have h_cl_sub :
            closure (interior (A : Set X))
              ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_sub
        -- step 3: take interiors again
        exact interior_mono h_cl_sub
      exact h_subset hx_intA
  | inr hxB =>
      -- `x ∈ interior (closure (interior B))`
      have hx_intB : x ∈ interior (closure (interior (B : Set X))) := hB hxB
      -- analogous inclusion for `B`
      have h_subset :
          interior (closure (interior (B : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) := by
        have h_int_sub : interior (B : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        have h_cl_sub :
            closure (interior (B : Set X))
              ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_sub
        exact interior_mono h_cl_sub
      exact h_subset hx_intB