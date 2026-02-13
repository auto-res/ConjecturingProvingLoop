

theorem P2_to_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hA
  exact hA.trans interior_subset

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ closure (interior A) := hA hAx
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact hsubset hxA
  | inr hBx =>
      have hxB : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact hsubset hxB

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hAopen
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hAopen.interior_eq] using hx
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact h_subset hx_int

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → interior A ⊆ interior (closure (interior A)) := by
  intro hP2
  exact interior_subset.trans hP2