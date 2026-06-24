

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset

theorem Topology.P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  exact hP2.trans (interior_mono (closure_mono interior_subset))

theorem Topology.P1_iff_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using this
    exact subset_antisymm h₁ h₂
  · intro hEq
    have hsubset : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq.symm] using hsubset

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_closure :
            closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            exact Set.subset_union_left
          exact closure_mono h_int
        exact interior_mono h_closure
      exact hsubset hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_closure :
            closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            exact Set.subset_union_right
          exact closure_mono h_int
        exact interior_mono h_closure
      exact hsubset hx_int