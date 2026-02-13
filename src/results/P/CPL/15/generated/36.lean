

theorem P1_antisymm {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) (hAB : A ⊆ B) (hBA : B ⊆ A) : closure (interior A) = closure (interior B) := by
  have hEq : (A : Set X) = B := Set.Subset.antisymm hAB hBA
  simpa [hEq]

theorem P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : A ⊆ interior (closure A) := by
  intro x hx
  -- Use the `P2` hypothesis to go one step up in the chain
  have hx₁ : x ∈ interior (closure (interior A)) := hA hx
  -- Relate the two interiors through monotonicity
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
  exact h_subset hx₁

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hd : closure (interior A) = Set.univ) : P1 A := by
  intro x hx
  simpa [hd.symm] using (Set.mem_univ x)