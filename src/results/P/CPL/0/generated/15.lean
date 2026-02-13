

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P3 A → P2 A := by
  intro hP1 hP3
  intro x hxA
  -- First, show the closures of `A` and `interior A` coincide.
  have h_closure_subset : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hP1)
  have h_subset' : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  have h_closure_eq : closure (interior A) = closure (A : Set X) :=
    subset_antisymm h_subset' h_closure_subset
  -- Use `P3` together with the equality of closures to obtain the desired result.
  have hx_in : x ∈ interior (closure (A : Set X)) := hP3 hxA
  simpa [h_closure_eq] using hx_in

theorem exists_open_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ U ⊆ A ∧ P2 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (P2_interior (A := A))