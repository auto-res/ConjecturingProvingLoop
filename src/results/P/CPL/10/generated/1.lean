

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P3 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : (interior (closure (interior A)) : Set X) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact hsubset hx'

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P1 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'

theorem P1_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : Topology.P1 (closure A) := by
  intro x hx
  -- First inclusion: `closure A ⊆ closure (interior A)`
  have h₁ : (closure A : Set X) ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := h
    simpa [closure_closure] using closure_mono hA
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    exact
      closure_mono
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
  exact h₂ (h₁ hx)

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` is in `A`
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- Show the bigger set contains the smaller one
      have hsubset :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA'
  | inr hxB =>
      -- `x` is in `B`
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB'

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  intro x hx
  -- `interior A` is open and contained in its closure, hence contained in the
  -- interior of that closure
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  -- Apply the inclusion to the given element
  have : x ∈ interior (closure (interior A)) := hsubset hx
  -- Rewriting `interior (interior A)` to `interior A`
  simpa [isOpen_interior.interior_eq] using this

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  have hx_int : x ∈ interior (Set.univ : Set X) := by
    simpa [isOpen_univ.interior_eq] using hx
  have hx_closure : x ∈ closure (interior (Set.univ : Set X)) :=
    subset_closure hx_int
  simpa using hx_closure

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` belongs to `A`
      have hxA' : x ∈ interior (closure A) := hA hxA
      -- Show the required inclusion of interiors of closures
      have hsubset :
          (interior (closure A) : Set X) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA'
  | inr hxB =>
      -- `x` belongs to `B`
      have hxB' : x ∈ interior (closure B) := hB hxB
      have hsubset :
          (interior (closure B) : Set X) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB'

theorem exists_nonempty_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P1 A := by
  classical
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  ·
    rcases ‹Nonempty X› with ⟨x⟩
    exact ⟨x, by simp⟩
  ·
    simpa using Topology.P1_univ