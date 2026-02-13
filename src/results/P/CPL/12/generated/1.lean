

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using
    (subset_closure : (interior A) ⊆ closure (interior A)) hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure A) := hA hxA
      have hmono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure A ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono hcl
      exact hmono hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure B) := hB hxB
      have hmono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure B ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono hcl
      exact hmono hx'

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx