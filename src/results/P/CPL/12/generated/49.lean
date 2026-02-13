

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P1 A → P1 B → P1 C → P1 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First combine `A` and `B`
  have hAB : P1 (A ∪ B) := P1_union (A := A) (B := B) hA hB
  -- Then add `C`
  have hABC : P1 ((A ∪ B) ∪ C) := P1_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite the union to the required form
  simpa [Set.union_assoc] using hABC

theorem P1_iff_P2_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → (P1 A ↔ P2 A) := by
  intro hCl
  have hP1_to_P2 : P1 A → P2 A := by
    intro hP1
    intro x _
    -- From `hP1` we get `closure (interior A) = closure A = univ`.
    have h_cl_int_univ : closure (interior (A : Set X)) = (Set.univ : Set X) := by
      have hEq := closure_interior_eq_closure_of_P1 (A := A) hP1
      simpa [hCl] using hEq
    -- Hence the interior of this closure is the whole space.
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_cl_int_univ, interior_univ] using this
  exact ⟨hP1_to_P2, P1_of_P2⟩