

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure (interior A)) := hA hAx
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure (interior B)) := hB hBx
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxB

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hAopen x hx
  simpa [hAopen.interior_eq] using (P3_of_open hAopen) hx

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P3 A) → P3 (⋃₀ 𝒜) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : P3 A := hP3 A hA_mem
  have hx_int_clA : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_sUnion_of_mem hA_mem
  exact hsubset hx_int_clA