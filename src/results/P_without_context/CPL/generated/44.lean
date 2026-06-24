

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P1 A := by
  intro x hxA
  exact interior_subset (h hxA)

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A := by
  intro x hxA
  -- Since `A` is open, it coincides with its interior
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  -- `interior A` is contained in `interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    have h : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (subset_closure : interior A ⊆ closure (interior A))
    simpa [interior_interior] using h
  exact h_subset hx_int

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ closure (interior A) := hA hxA
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono (by
            intro y hy
            exact Or.inl hy))
      exact h_sub hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ closure (interior B) := hB hxB
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono (by
            intro y hy
            exact Or.inr hy))
      exact h_sub hxB'

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have h_int : interior A ⊆ interior (A ∪ B) := by
          have h_set : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_set
        exact closure_mono h_int
      exact interior_mono h_sub hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      -- `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h_int : interior B ⊆ interior (A ∪ B) := by
          have h_set : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_set
        exact closure_mono h_int
      exact interior_mono h_sub hxB'

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    · exact closure_mono (interior_subset)
    ·
      have h_closed : IsClosed (closure (interior A)) := isClosed_closure
      exact closure_minimal hP1 h_closed
  · intro h_eq
    intro x hxA
    have hx_closureA : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hx_closureA