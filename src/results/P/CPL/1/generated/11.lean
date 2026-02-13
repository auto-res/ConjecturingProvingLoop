

theorem exists_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P1 A ∧ closure A = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P1_univ
  · simpa [closure_univ]

theorem P2_bunion {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B ∪ (A ∩ B)) := by
  -- First obtain `P2` for `A ∪ B`.
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  -- Show that adding `A ∩ B` does not change the union.
  have h_eq : (A ∪ B ∪ (A ∩ B) : Set X) = A ∪ B := by
    -- Rewrite with associativity to apply `Set.union_eq_left`.
    have h_assoc : (A ∪ B ∪ (A ∩ B)) = (A ∪ B) ∪ (A ∩ B) := by
      simpa [Set.union_assoc]
    -- Since `A ∩ B ⊆ A ∪ B`, we can collapse the union.
    have h_sub : (A ∩ B : Set X) ⊆ A ∪ B := by
      intro x hx
      exact Or.inl hx.1
    have h_union : ((A ∪ B) ∪ (A ∩ B) : Set X) = A ∪ B :=
      (Set.union_eq_left).2 h_sub
    simpa [h_assoc] using h_union
  -- Prove the desired `P2` property.
  intro x hx
  -- Convert the hypothesis to membership in `A ∪ B`.
  have hxAB : x ∈ A ∪ B := by
    simpa [h_eq] using hx
  -- Apply `P2` for `A ∪ B`.
  have hx_int : x ∈ interior (closure (interior (A ∪ B))) := hAB hxAB
  -- Rewrite back to the required set using the equality.
  simpa [h_eq] using hx_int