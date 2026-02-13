

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact (interior_mono (closure_mono interior_subset)) hx

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have : x ∈ interior (closure A) := by
    simpa [hA, interior_univ] using (Set.mem_univ x)
  exact this

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact h_subset hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact h_subset hx'

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` belongs to `A`
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      -- Show the needed inclusion of interiors
      have h_subset : interior (closure (interior A)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_subset hx'
  | inr hxB =>
      -- `x` belongs to `B`
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      -- Show the needed inclusion of interiors
      have h_subset : interior (closure (interior B)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_subset hx'

theorem closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P3 A) : closure A = closure (interior (closure A)) := by
  -- First, rewrite the `P3` hypothesis as an inclusion we can use.
  have h_sub : (A : Set X) ⊆ interior (closure A) := by
    simpa [Topology.P3] using hA
  -- Prove the desired equality via two inclusions.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior (closure A))`
    have : closure A ⊆ closure (interior (closure A)) := closure_mono h_sub
    simpa using this
  · -- `closure (interior (closure A)) ⊆ closure A`
    have : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono (interior_subset : interior (closure A) ⊆ closure A)
    simpa [closure_closure] using this