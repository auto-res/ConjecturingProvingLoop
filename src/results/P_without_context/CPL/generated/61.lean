

theorem Topology.P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  dsimp [P1]
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem Topology.P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact hsubset hx'

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [P3] at *
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x ∈ A`
      have hxA : x ∈ interior (closure A) := hA hAx
      -- `closure A ⊆ closure (A ∪ B)`
      have hsub : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have hcl : closure A ⊆ closure (A ∪ B) := closure_mono hsub
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hcl
      exact hsubset hxA
  | inr hBx =>
      -- `x ∈ B`
      have hxB : x ∈ interior (closure B) := hB hBx
      -- `closure B ⊆ closure (A ∪ B)`
      have hsub : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hcl : closure B ⊆ closure (A ∪ B) := closure_mono hsub
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hcl
      exact hsubset hxB

theorem Topology.exists_closed_subset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : ∃ B : Set X, IsClosed B ∧ B ⊆ A ∧ Topology.P2 B := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, ?_⟩
  simpa [P2] using (Set.empty_subset _)