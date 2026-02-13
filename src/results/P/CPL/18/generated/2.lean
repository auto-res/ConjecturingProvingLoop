

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  dsimp [P3]
  simpa [interior_interior] using
    (interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A)))

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx'

theorem exists_P3_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, A ⊆ U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · intro x hx
    trivial
  · dsimp [Topology.P3]
    intro x hx
    simpa [closure_univ, interior_univ] using hx