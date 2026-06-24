

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have hsub : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset))
  exact fun x hx => hsub (hP2 hx)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hP1A hP1B
  unfold P1 at *
  intro x hx
  cases hx with
  | inl hA =>
      have hxA : x ∈ closure (interior A) := hP1A hA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hxA
  | inr hB =>
      have hxB : x ∈ closure (interior B) := hP1B hB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hxB

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hP2A hP2B
  unfold P2 at *
  intro x hx
  cases hx with
  | inl hA =>
      have hxA : x ∈ interior (closure (interior A)) := hP2A hA
      have hsubset : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hxA
  | inr hB =>
      have hxB : x ∈ interior (closure (interior B)) := hP2B hB
      have hsubset : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hxB

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  dsimp [P3]
  exact interior_maximal subset_closure hA

theorem P1_self {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  dsimp [P1]
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this