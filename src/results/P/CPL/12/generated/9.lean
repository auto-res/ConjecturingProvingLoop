

theorem P2_iUnion {X : Type*} {ι : Sort*} [TopologicalSpace X] {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (Set.iUnion A) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hP2 : P2 (A i) := hAll i
  have hx' : x ∈ interior (closure (interior (A i))) := hP2 hxAi
  have hsubset : interior (closure (interior (A i))) ⊆
      interior (closure (interior (Set.iUnion A))) := by
    have hInt : interior (A i) ⊆ interior (Set.iUnion A) := by
      have hAi_sub : (A i : Set X) ⊆ Set.iUnion A :=
        Set.subset_iUnion _ _
      exact interior_mono hAi_sub
    have hcl : closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) :=
      closure_mono hInt
    exact interior_mono hcl
  exact hsubset hx'

theorem P3_iUnion {X : Type*} {ι : Sort*} [TopologicalSpace X] {A : ι → Set X} : (∀ i, P3 (A i)) → P3 (Set.iUnion A) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hP3 : P3 (A i) := hAll i
  have hx' : x ∈ interior (closure (A i)) := hP3 hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (Set.iUnion A)) := by
    have hcl : closure (A i) ⊆ closure (Set.iUnion A) := by
      have hAi_sub : (A i : Set X) ⊆ Set.iUnion A := Set.subset_iUnion _ _
      exact closure_mono hAi_sub
    exact interior_mono hcl
  exact hsubset hx'

theorem P1_iff_P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X} (hA₁ : IsOpen A) (hA₂ : IsClosed A) : P1 A ↔ P2 A := by
  have hInt : interior (A : Set X) = A := hA₁.interior_eq
  have hP1_to_P2 : P1 A → P2 A := by
    intro _hP1
    intro x hx
    simpa [hInt, hA₂.closure_eq] using hx
  exact ⟨hP1_to_P2, P1_of_P2⟩

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  have hInt : interior (A : Set X) = A := hA.interior_eq
  simpa [P2, P3, hInt]