

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  intro x hxA
  exact interior_subset (hP2 hxA)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      have hInt_sub : interior A ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inl hy)
      have hClosure_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt_sub
      exact hClosure_sub hx_closureA
  | inr hxB =>
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      have hInt_sub : interior B ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inr hy)
      have hClosure_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt_sub
      exact hClosure_sub hx_closureB

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using h
  ·
    exact closure_mono interior_subset

theorem P3_of_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P2 A → Topology.P3 A := by
  intro _ hP2
  dsimp [Topology.P3] at *
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact h_subset hx_int

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  exact Set.empty_subset _

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx