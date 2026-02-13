

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : P1 (A i) := h i
  have hx_cl : x ∈ closure (interior (A i)) := hPi hxi
  have h_subset :
      (closure (interior (A i)) : Set X) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono (interior_mono (Set.subset_iUnion A i))
  exact h_subset hx_cl

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  intro x hx
  classical
  -- In a subsingleton space, any non-empty set is the whole space.
  have hAu : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have hxy : y = x := Subsingleton.elim y x
      simpa [hxy] using hx
  -- Rewriting gives the desired membership.
  simpa [hAu, closure_univ, interior_univ]