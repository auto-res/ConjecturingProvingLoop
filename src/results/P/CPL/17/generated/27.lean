

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  exact (P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩

theorem exists_open_between_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ interior (closure A) ⊆ U := by
  intro hP2
  have hP3 : P3 A := P2_implies_P3 (A := A) hP2
  refine ⟨interior (closure A), isOpen_interior, ?_, subset_rfl⟩
  exact hP3

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P3 A → Topology.P3 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP3A
  simpa using
    (P3_prod (A := A) (B := (Set.univ : Set Y)) hP3A (P3_univ (X := Y)))

theorem P2_induction_on_closure {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ closure A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ A) → Topology.P2 A := by
  intro h x hxA
  -- `x` lies in the closure of `A`
  have hx_cl : (x : X) ∈ closure A := subset_closure hxA
  -- obtain an open neighbourhood of `x` contained in `A`
  rcases h x hx_cl with ⟨U, hU_open, hxU, hU_sub_A⟩
  -- this neighbourhood sits inside `interior A`
  have hU_sub_int : (U : Set X) ⊆ interior A :=
    interior_maximal hU_sub_A hU_open
  have hx_intA : x ∈ interior A := hU_sub_int hxU
  -- `interior A` is an open subset of `closure (interior A)`
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  -- conclude
  exact hsubset hx_intA