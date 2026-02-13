

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ closure (interior A) := hA hxA
      have hmono : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hsubset : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset
      exact hmono hx'
  | inr hxB =>
      have hx' : x ∈ closure (interior B) := hB hxB
      have hmono : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hsubset : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset
      exact hmono hx'