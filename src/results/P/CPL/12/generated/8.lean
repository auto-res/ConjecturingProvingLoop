

theorem P3_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A ↔ P1 A := by
  -- First, note that `closure A = univ`, since it contains `closure (interior A) = univ`.
  have hClosureA : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · simp
    · simpa [h] using
        (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
  -- Rewrite the two predicates with these equalities and finish by `simp`.
  unfold P3 P1
  simpa [h, hClosureA]

theorem P1_iUnion {X : Type*} {ι : Sort*} [TopologicalSpace X] {A : ι → Set X} : (∀ i, P1 (A i)) → P1 (Set.iUnion A) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hP1 : P1 (A i) := hAll i
  have hx' : x ∈ closure (interior (A i)) := hP1 hxi
  have hsubset :
      closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) := by
    have hInt : interior (A i) ⊆ interior (Set.iUnion A) := by
      have hAi_sub : (A i : Set X) ⊆ Set.iUnion A := by
        exact Set.subset_iUnion _ _
      exact interior_mono hAi_sub
    exact closure_mono hInt
  exact hsubset hx'

theorem P2_univ_iff {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P2_univ