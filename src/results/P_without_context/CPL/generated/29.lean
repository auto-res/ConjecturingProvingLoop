

theorem P2_imp_P1_of_T1 {X : Type*} [TopologicalSpace X] [T1Space X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact hP2.trans (interior_subset)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hPA hPB
  -- The closure of the interior of `A` (resp. `B`) is contained in the closure of the
  -- interior of `A ∪ B`.
  have hA_closure :
      closure (interior A) ⊆ closure (interior (A ∪ B)) := by
    refine closure_mono ?_
    refine interior_mono ?_
    intro x hx
    exact Or.inl hx
  have hB_closure :
      closure (interior B) ⊆ closure (interior (A ∪ B)) := by
    refine closure_mono ?_
    refine interior_mono ?_
    intro x hx
    exact Or.inr hx
  -- Now put the two inclusions together.
  have hA' : A ⊆ closure (interior (A ∪ B)) := fun x hx => hA_closure (hPA hx)
  have hB' : B ⊆ closure (interior (A ∪ B)) := fun x hx => hB_closure (hPB hx)
  exact Set.union_subset hA' hB'

theorem exists_dense_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P2 A ∧ Dense A := by
  refine ⟨(Set.univ : Set X), ?_, dense_univ⟩
  intro x hx
  simp