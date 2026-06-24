

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P1 A := by
  intro x hx
  exact interior_subset (h hx)

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hxA : x ∈ closure (interior A) := hA hA_mem
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inl hy))
      exact h_sub hxA
  | inr hB_mem =>
      -- `x ∈ B`
      have hxB : x ∈ closure (interior B) := hB hB_mem
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inr hy))
      exact h_sub hxB

theorem P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro h
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have h_sub : closure (interior A) ⊆ closure A := by
    have : (interior A : Set X) ⊆ A := interior_subset
    exact closure_mono this
  exact (interior_mono h_sub) hx'

theorem exists_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa [Dense, closure_univ]
  · exact P1_univ