

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P3 A := by
  intro x hxA
  have hx1 : x ∈ interior (closure (interior A)) := h hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx1

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Sort _} {A : ι → Set X} (hA : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_cl : x ∈ closure (interior (A i)) := (hA i) hxi
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    have h_sub : interior (A i) ⊆ interior (⋃ j, A j) :=
      interior_mono (Set.subset_iUnion _ i)
    exact closure_mono h_sub
  exact hsubset hx_cl

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  intro x hxA
  -- The interior of an open set is the set itself.
  have h_int : interior A = A := hA.interior_eq
  -- Hence `x` is in the interior of `A`.
  have hx_int : x ∈ interior A := by
    simpa [h_int] using hxA
  -- Monotonicity of `interior` gives the desired inclusion.
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact h_subset hx_int

theorem P1_iff_denseInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro h
    apply le_antisymm
    · exact closure_mono interior_subset
    ·
      have h_closed : IsClosed (closure (interior A)) := isClosed_closure
      exact closure_minimal h h_closed
  · intro h_eq
    intro x hxA
    have : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using this